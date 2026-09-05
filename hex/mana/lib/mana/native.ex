defmodule Mana.Native do
  @moduledoc """
  Marker for modules whose function bodies live in a native crate. The crate
  ships with the Hex package under `native/<pkg>/`. The idea is close to
  `use Rustler`, but the target is the closed-world single-binary build of
  mana.

  ## Usage

      defmodule :my_pkg_native do
        use Mana.Native, otp_app: :my_pkg, package: :my_pkg
        # BEAM fallback — runs on plain Elixir; cut on mana:
        def hello(_), do: {:error, :not_supported_on_beam}
      end

  On BEAM the bodies that you write here run as ordinary Elixir. On mana the
  package ships a Rust crate at `native/<package>/`. The crate exports
  `#[no_mangle]` symbols named `<module>_<fun>_<arity>`. The compiler finds
  the `mana_native:` mix metadata of the dep, builds the crate with cargo,
  and lowers calls to this module directly to those symbols.

  This macro is a documentation and marker hook. It does not generate native
  code. The `mana_native:` keyword in the `mix.exs` of the dep drives the
  discovery:

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
