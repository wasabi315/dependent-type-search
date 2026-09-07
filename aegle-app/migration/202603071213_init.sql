CREATE TYPE result_head AS ENUM (
    'U',
    'Var',
    'Top',
    'Sigma',
    'Proj1',
    'Proj2'
);

CREATE TYPE polymorphic AS ENUM (
    'Monomorphic',
    'Polymorphic'
);

CREATE TYPE kind AS ENUM (
    'Postulate',
    'Function',
    'Datatype',
    'Record',
    'Constructor',
    'Primitive'
);

CREATE TABLE library_items (
    id                   bigint            GENERATED ALWAYS AS IDENTITY PRIMARY KEY,

    canonical_name       text              NOT NULL,  -- Can't be UNIQUE because we have overloaded record constructors
    kind                 kind              NOT NULL,
    signature            bytea             NOT NULL,
    original_signature   bytea             NOT NULL,
    body                 bytea,                       -- NULL for opaque definitions

    -- Features
    arity                int               NOT NULL,
    arity_has_var        boolean           NOT NULL,
    polymorphic          polymorphic       NOT NULL,
    result_head          result_head       NOT NULL,
    result_head_top      text,                       -- NULL unless result_head = 'Top'

    -- meta info
    module_name          text              NOT NULL,
    position             int               NOT NULL

    CONSTRAINT result_head_top_check CHECK (
        (result_head = 'Top'  AND result_head_top IS NOT NULL) OR
        (result_head <> 'Top' AND result_head_top IS NULL)
    )
);

CREATE TABLE exports (
    id                   bigint            GENERATED ALWAYS AS IDENTITY PRIMARY KEY,
    canonical_name       text              NOT NULL,
    export_as_qual       text              NOT NULL, -- include lib name
    export_as_qual_      text              NOT NULL, -- does not include lib name
    export_as_unqual     text              NOT NULL
);

CREATE MATERIALIZED VIEW exports_unqual AS
SELECT DISTINCT export_as_unqual, canonical_name
FROM exports;

CREATE MATERIALIZED VIEW exports_qual AS
SELECT DISTINCT export_as_qual, export_as_qual_, canonical_name
FROM exports;

CREATE INDEX ON exports_qual   (export_as_qual_, canonical_name);
CREATE INDEX ON exports_unqual (export_as_unqual, canonical_name);
CREATE INDEX ON library_items  (result_head, result_head_top);
