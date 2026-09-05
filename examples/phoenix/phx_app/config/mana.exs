import Config

# The :mana env is the native-build env. mix mana.compile runs under
# MIX_ENV=mana. It mirrors the dev endpoint with release semantics.
# config/runtime.exs starts the server and reads PHX_SERVER and PORT at
# native boot. A fixed secret is baked in. The dev-only affordances
# (code_reloader, live_reload, watchers) are off. config/config.exs swaps
# the JSON library to ManaJSON when config_env() == :mana.
config :phx_app, PhxAppWeb.Endpoint,
  http: [ip: {127, 0, 0, 1}],
  check_origin: false,
  code_reloader: false,
  debug_errors: false,
  secret_key_base: "/vzudvhAvuQ7fdMQjUrysevl5N7gpSTGGQRsnRqGMljDulvDfj/jsXRpEwJOBuMg",
  watchers: []

config :logger, :default_formatter, format: "[$level] $message\n"
