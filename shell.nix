let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/24.05";
  pkgs = import nixpkgs {};
in
pkgs.mkShell {
    name = "Chrobelias";
    packages = [ 
      # Treesitter-parsers
      pkgs.vimPlugins.nvim-treesitter-parsers.ocaml 
      pkgs.vimPlugins.nvim-treesitter-parsers.yaml
      pkgs.vimPlugins.nvim-treesitter-parsers.jsonc
      pkgs.vimPlugins.nvim-treesitter-parsers.markdown
      pkgs.vimPlugins.nvim-treesitter-parsers.markdown_inline
      pkgs.vimPlugins.nvim-treesitter-parsers.nix

      # Build tools
      pkgs.opam
    ];
    shellHook = "eval $(opam env)";
}
