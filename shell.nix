{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
    name = "Chrobelias";
    packages = with pkgs; [ 
      gmp
    ];
}
