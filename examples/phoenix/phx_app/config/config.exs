# This file configures the application and its dependencies with the
# Config module.
#
# This configuration file loads before any dependency and applies only
# to this project.

import Config

config :phx_app,
  generators: [timestamp_type: :utc_datetime]

config :phx_app, PhxAppWeb.Endpoint,
  url: [host: "localhost"],
  adapter: Bandit.PhoenixAdapter,
  render_errors: [
    formats: [html: PhxAppWeb.ErrorHTML, json: PhxAppWeb.ErrorJSON],
    layout: false
  ],
  pubsub_server: PhxApp.PubSub,
  live_view: [signing_salt: "rl9uueu0"]

config :logger, :default_formatter,
  format: "$time $metadata[$level] $message\n",
  metadata: [:request_id]

# JSON library: the native ManaJSON (serde) under the :mana build, Jason on
# BEAM. Under a non-mana env ManaJSON does not even compile (see mix.exs:
# mana_json is only: [:mana]), so this is the single switch point.
config :phoenix,
       :json_library,
       if(config_env() == :mana, do: ManaJSON, else: Jason)

# Import the environment specific config. This must stay at the bottom
# of this file so that it overrides the configuration above.
import_config "#{config_env()}.exs"
