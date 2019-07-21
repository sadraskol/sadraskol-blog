{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
    "sadraskol"
, dependencies =
    [ "aff"
    , "affjax"
    , "console"
    , "css"
    , "datetime"
    , "effect"
    , "formatters"
    , "halogen"
    , "js-date"
    , "prelude"
    , "psci-support"
    , "simple-json"
    ]
, packages =
    ./packages.dhall
, sources =
    [ "src/**/*.purs", "test/**/*.purs" ]
}
