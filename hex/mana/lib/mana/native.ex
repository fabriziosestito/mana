defmodule Mana.Native do
  @moduledoc """
  Marker for modules whose function bodies are implemented in a native
  crate shipped alongside the Hex package under `native/<pkg>/`, in the
  spirit of `use Rustler` but targeting mana's closed-world single-binary
  build.

  ## Usage

      defmodule :my_pkg_native do
        use Mana.Native, otp_app: :my_pkg, package: :my_pkg
        # BEAM fallback — runs on plain Elixir; cut on mana:
        def hello(_), do: {:error, :not_supported_on_beam}
      end

  On BEAM the bodies you write here run as ordinary Elixir. On mana the
  package ships a Rust crate at `native/<package>/` that exports
  `#[no_mangle]` symbols named `<module>_<fun>_<arity>`; the compiler
  discovers the dep's `mana_native:` mix metadata, cargo-builds the crate,
  and lowers calls to this module straight to those symbols.

  This macro is a documentation/marker hook — it does not generate native
  code. Discovery is driven by the `mana_native:` keyword in the dep's
  `mix.exs`:

      def project do
        [
          app: :my_pkg,
          mana_native: [packages: [{:my_pkg, [module: "my_pkg_native"]}]],
          ...
        ]
      end
  """

  defmacro __using__(opts) do
    otp_app = Keyword.fetch!(opts, :otp_app)
    package = Keyword.get(opts, :package, otp_app)

    quote do
      @mana_native_otp_app unquote(otp_app)
      @mana_native_package unquote(package)
      def __mana_native__,
        do: %{otp_app: @mana_native_otp_app, package: @mana_native_package}
    end
  end
end
