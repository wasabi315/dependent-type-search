module Aegle.Web
  ( runServer,
    Config (..),
  )
where

import Aegle.Core.Name
import Aegle.Core.Term (Unqualified (..))
import Aegle.Database.Backend
import Aegle.Prelude
import Aegle.Search qualified as Search
import Aegle.Search.Term
import Data.Aeson (ToJSON)
import Data.Text qualified as T
import Data.Time.Clock
import Lucid hiding (for_)
import Lucid.Servant
import Network.URI.Encode qualified
import Network.Wai.Handler.Warp qualified as Warp
import Network.Wai.Middleware.RequestLogger
import Paths_aegle_app
import Prettyprinter
import Servant
import Servant.HTML.Lucid
import System.FilePath

--------------------------------------------------------------------------------

data Config = Config
  { port :: Warp.Port,
    dbReader :: DbReader IO,
    agdaHtmlDir :: FilePath,
    timeout :: Int
  }

runServer :: Config -> IO ()
runServer Config {..} = do
  dataDir <- getDataDir
  let staticDir = dataDir </> "static"
  putStrLn $ "Listening on port " ++ show port
  let app =
        server staticDir agdaHtmlDir dbReader timeout
          & serve api
          & logStdout
  Warp.run port app

--------------------------------------------------------------------------------
-- APIs

type API =
  SearchAPI
    :<|> SearchUI
    :<|> "ping" :> Get '[PlainText] T.Text
    :<|> "static" :> Raw -- static assets like css/js
    :<|> "agda" :> Raw -- Agda HTML

type SearchAPI =
  "search"
    :> QueryParam' '[Required, Strict] "q" T.Text
    :> Get '[JSON] Result

type SearchUI =
  QueryParam "q" T.Text
    :> Get '[HTML] (Html ())

api :: Proxy API
api = Proxy

server :: FilePath -> FilePath -> DbReader IO -> Int -> Server API
server staticDir agdaHtmlDir dbReader timeout =
  search dbReader timeout
    :<|> searchUI dbReader timeout
    :<|> pure "pong"
    :<|> serveDirectoryFileServer staticDir
    :<|> serveDirectoryFileServer agdaHtmlDir

--------------------------------------------------------------------------------
-- JSON API

data Result = Result
  { numCands :: Int,
    time :: NominalDiffTime,
    matches :: [Match]
  }
  deriving stock (Show, Generic)
  deriving (ToJSON) via Generically Result

data Match = Match
  { canonicalName :: T.Text,
    kind :: T.Text,
    reexportedAs :: [T.Text],
    signature :: T.Text,
    originalSignature :: T.Text,
    iso :: T.Text,
    solution :: T.Text,
    moduleName :: T.Text,
    position :: Int
  }
  deriving stock (Show, Generic)
  deriving (ToJSON) via Generically Match

search :: DbReader IO -> Int -> Server SearchAPI
search dbReader timeout = \query -> do
  guard (not $ T.null $ T.strip query)
    ??: err400 {errBody = "Query parameter q must not be empty"}
  result <-
    liftIO (Search.search config query)
      ?% convertError
  pure $! convertResult result
  where
    config =
      Search.Config
        { querySrc = "<query param>",
          recordCandTimes = False,
          ..
        }

    convertResult Search.Result {..} = do
      let sorted = sortOn (termSize . (.solution)) matches
      Result {matches = map convertMatch sorted, ..}

    convertMatch Search.Match {item = LibraryItem {..}, ..} =
      Match
        { canonicalName = T.show $ pretty canonicalName,
          kind = convertDefKind kind,
          reexportedAs = T.show . pretty <$> reexportedAs,
          signature = T.show $ pretty $ Unqualified signature,
          originalSignature = T.show $ pretty $ Unqualified originalSignature,
          iso = T.show $ pretty iso,
          solution = T.show $ pretty $ Unqualified solution,
          moduleName = T.show $ pretty moduleName,
          ..
        }

    convertDefKind = \case
      DKPostulate -> "postulate"
      DKFunction -> "function"
      DKDatatype -> "data"
      DKRecord -> "record"
      DKConstructor -> "constructor"
      DKPrimitive -> "primitive"

    convertError e = case e of
      Search.ParseError {} -> err400 {errBody = fromString $ displayException e}
      Search.NotFound {} -> err404 {errBody = fromString $ displayException e}
      Search.Timeout -> err422 {errBody = fromString $ displayException e}

--------------------------------------------------------------------------------
-- Web interface

searchUI :: DbReader IO -> Int -> Server SearchUI
searchUI dbReader timeout = \query -> do
  let query' = filter (not . T.null . T.strip) query
  result <- for query' $ liftIO . Search.search config

  pure $ layoutHtml do
    h1_ do
      a_ [hrefTop Nothing] "Aegle 🦅"

    form_ [id_ "search-form", method_ "get", action_ "/"] do
      input_
        [ type_ "search",
          name_ "q",
          placeholder_ "Query type",
          value_ $ fromMaybe "" query,
          autofocus_
        ]
      button_ [type_ "submit"] do
        span_ [class_ "search-spinner"] mempty
        "Search"

    case result of
      Nothing -> introHtml
      Just (Right result) -> resultHtml result
      Just (Left e) ->
        pre_ $ code_ [class_ "error"] $ toHtml $ displayException e
  where
    config =
      Search.Config
        { querySrc = "<query param>",
          recordCandTimes = False,
          ..
        }

    hrefTop = safeAbsHref_ @SearchUI api Proxy

    -- Ref: Agda.Interaction.Highlighting.HTML.Base.annotate
    hrefDefSite modName pos =
      href_
        $ T.pack
        $ concat
          [ "/agda/",
            Network.URI.Encode.encode $ T.unpack (coerce modName),
            ".html#",
            Network.URI.Encode.encode $ show pos
          ]

    introHtml :: Html ()
    introHtml = do
      p_ [class_ "intro"] "Type-based library search for Agda"
      section_ do
        h2_ "Example queries"
        ul_ do
          li_ do
            exampleHtml
              "Search by type"
              ": (m n : Nat) → _≡_ Nat (_*_ m n) 1 → _≡_ Nat m 1"
          li_ do
            exampleHtml
              "Isomorphism and instantiation"
              ": (A B : Set) → (A → B) → A → B"
          li_ do
            exampleHtml
              "Type alias expansion"
              ": (m n : Nat) → _≡_ Nat (_+_ m n) (_+_ n m)"
          li_ do
            exampleHtml
              "Filtering by name substrings"
              "* < : (m n o p : ℕ) → _<_ m n → _<_ o p → _<_ (_*_ m o) (_*_ n p)"
      where
        exampleHtml label query = do
          toHtml @T.Text label
          ": "
          a_ [hrefTop (Just query)] do
            code_ [class_ "example-query"] do
              toHtml @T.Text query

    kindHtml :: DefKind -> Html ()
    kindHtml = \case
      DKPostulate -> "postulate"
      DKFunction -> "function"
      DKDatatype -> "data"
      DKRecord -> "record"
      DKConstructor -> "constructor"
      DKPrimitive -> "primitive"

    resultHtml :: Search.Result -> Html ()
    resultHtml Search.Result {..} = do
      let numMatches = length matches
          sorted = sortOn (termSize . (.solution)) matches

      p_ [class_ "meta"] do
        toHtml $ T.show numMatches
        " item(s) matched in "
        toHtml $ T.show numCands
        " candidate(s). Took "
        toHtml $ T.show time
        "."
      case matches of
        [] -> p_ "No matches."
        _ -> ul_ [class_ "match-list"] do
          for_ sorted \Search.Match {item = LibraryItem {..}, ..} -> li_ [class_ "match"] do
            code_ [class_ "match-heading"] do
              span_ [class_ "def-kind"] do
                kindHtml kind
                " "
              span_ [class_ "match-main"] do
                a_ [hrefDefSite moduleName position] do
                  strong_ $ toHtml $ T.show (pretty canonicalName.moduleName <> "." <> pretty canonicalName.name)
                " :"
                wbr_ []
                " "
                prettyHtml $ Unqualified originalSignature
            div_ [class_ "match-details"] do
              p_ [class_ "detail-row"] do
                strong_ "From: "
                code_ $ prettyHtml canonicalName.libName
              unless (null reexportedAs) do
                p_ [class_ "detail-row"] do
                  strong_ "Re-exported as: "
                  sequence_ $ intersperse ", " do
                    reexportedAs <&> \name ->
                      code_ do
                        prettyHtml name.libName
                        " "
                        toHtml $ T.show (pretty name.moduleName <> "." <> pretty name.name)
              p_ [class_ "detail-row"] do
                strong_ "Solution: "
                code_ $ prettyHtml $ Unqualified solution

layoutHtml :: Html () -> Html ()
layoutHtml content = doctypehtml_ do
  head_ do
    title_ "Aegle"
    link_ [rel_ "stylesheet", type_ "text/css", href_ "/static/style.css"]
    meta_ [name_ "viewport", content_ "width=device-width, initial-scale=1"]
    meta_ [charset_ "utf-8"]
    link_ [rel_ "icon", href_ "data:image/svg+xml,<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 100 100%22><text y=%22.9em%22 font-size=%2290%22>🦅</text></svg>"]
  body_ do
    content
    script_ [src_ "/static/script.js"] (mempty @(Html ()))

prettyHtml :: (Pretty a, Monad m) => a -> HtmlT m ()
prettyHtml = toHtml . T.show . pretty
