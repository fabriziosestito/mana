# Compile-time config for the phx_app path dep (mirrors its own
# config/config.exs, which Mix never evaluates for path deps). Runtime
# endpoint env is seeded in Conf.Phx.go/0 — identically on both runtimes.
import Config

config :phx_app, PhxAppWeb.Endpoint,
  url: [host: "localhost"],
  adapter: Bandit.PhoenixAdapter,
  render_errors: [
    formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON],
    layout: false
  ],
  pubsub_server: PhxApp.PubSub,
  live_view: [signing_salt: "rl9uueu0"]

config :phoenix, :json_library, Jason
