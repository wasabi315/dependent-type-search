CREATE EXTENSION IF NOT EXISTS pg_trgm;

CREATE TABLE library_items (
    id                    bigserial PRIMARY KEY,
    name_qual             text      NOT NULL,
    name_unqual           text      NOT NULL,
    used_top_names_qual   text[]    NOT NULL,
    used_top_names_unqual text[]    NOT NULL,
    sig                   bytea     NOT NULL,
    body                  bytea                      -- NULL for axioms
);

CREATE INDEX items_name_unqual_trgm          ON library_items USING GIST (name_unqual gist_trgm_ops);
CREATE INDEX items_used_top_names_qual_gin   ON library_items USING gin (used_top_names_qual);
CREATE INDEX items_used_top_names_unqual_gin ON library_items USING gin (used_top_names_unqual);
