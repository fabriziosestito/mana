import Config

# The :mana env is the native-build env (mix mana.compile runs under
# MIX_ENV=mana). It mirrors dev's endpoint with release semantics: the
# server is started from config/runtime.exs (PHX_SERVER/PORT read at native
# boot), a fixed secret is baked, and the dev-only affordances
# (code_reloader/live_reload/watchers) are off. The JSON library is swapped
# to ManaJSON by config/config.exs (config_env() == :mana).
config :phx_app, PhxAppWeb.Endpoint,
  http: [ip: {127, 0, 0, 1}],
  check_origin: false,
  code_reloader: false,
  debug_errors: false,
  secret_key_base: "/vzudvhAvuQ7fdMQjUrysevl5N7gpSTGGQRsnRqGMljDulvDfj/jsXRpEwJOBuMg",
  watchers: []

config :logger, :default_formatter, format: "[$level] $message\n"
