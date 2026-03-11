CREATE EXTENSION IF NOT EXISTS pg_trgm;

CREATE TABLE library_items (
    id                   bigserial PRIMARY KEY,
    name_qual            text      NOT NULL,        -- Can't be UNIQUE because we have overloading
    name_unqual          text      NOT NULL,
    module               text      NOT NULL,
    sig                  bytea     NOT NULL,
    body                 bytea,                     -- NULL for axioms
    occurrence           boolean[],                 -- NULL for axioms
    noncanonish          text[]    NOT NULL,
    canonish             text[]    NOT NULL,

    -- Features
    arity                int       NOT NULL,
    polymorphic          int       NOT NULL,
    return_type_head     jsonb     NOT NULL,
    return_type_canonish text[] NOT NULL,

    return_sort_body     int,
    body_canonish        text[]
);

CREATE INDEX library_items_name_unqual_trgm    ON library_items USING GIST (name_unqual gist_trgm_ops);
CREATE INDEX library_items_feat_idx
  ON library_items (polymorphic, arity);
