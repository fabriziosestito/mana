# This file is responsible for configuring your application
# and its dependencies with the aid of the Config module.
#
# This configuration file is loaded before any dependency and
# is restricted to this project.

# General application configuration
import Config

config :phx_app,
  generators: [timestamp_type: :utc_datetime]

# Configure the endpoint
config :phx_app, PhxAppWeb.Endpoint,
  url: [host: "localhost"],
  adapter: Bandit.PhoenixAdapter,
  render_errors: [
    formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON],
    layout: false
  ],
  pubsub_server: PhxApp.PubSub,
  live_view: [signing_salt: "rl9uueu0"]

# Configure Elixir's Logger
config :logger, :default_formatter,
  format: "$time $metadata[$level] $message\n",
  metadata: [:request_id]

# JSON library: native ManaJSON (serde) under the :mana build, Jason on
# BEAM. Under a non-mana env ManaJSON is not even compiled (see mix.exs —
# mana_json is only: [:mana]), so this is the single switch point.
config :phoenix,
       :json_library,
       if(config_env() == :mana, do: ManaJSON, else: Jason)

# Import environment specific config. This must remain at the bottom
# of this file so it overrides the configuration defined above.
import_config "#{config_env()}.exs"
