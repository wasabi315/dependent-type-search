CREATE EXTENSION IF NOT EXISTS pg_trgm;

CREATE TABLE library_items (
    id              bigserial PRIMARY KEY,
    name_qual       text      NOT NULL,        -- Can't be UNIQUE because we have overloading
    name_unqual     text      NOT NULL,
    sig             bytea     NOT NULL,
    body            bytea,                     -- NULL for axioms

    -- Features
    arity           int       NOT NULL,
    polymorphic     int       NOT NULL,
    return_sort     int       NOT NULL
);

CREATE INDEX library_items_name_unqual_trgm    ON library_items USING GIST (name_unqual gist_trgm_ops);
