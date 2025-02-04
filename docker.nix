let
  pkgs = import ./support/nix/nixpkgs.nix;
  inherit (pkgs) lib;
  the-lab = import ./. { interactive = false; };
in
  pkgs.dockerTools.streamLayeredImage {
    name = "pltamy/1lab";
    tag = "latest";

    contents = with pkgs; the-lab.deps ++ [
      pkgsStatic.busybox # Need a shell, so go with static busybox

      # Needed for Github Actions:
      # gnutar
      # rsync
    ];

    config = {
      WorkingDir = "/workspace";
      Env = [
        "LANG=C.UTF-8" # Needed for GHC to set the correct encoding on handles

        # Needed for Github Actions:
        # "LD_LIBRARY_PATH=${lib.makeLibraryPath [ pkgs.stdenv.cc.cc ]}"
        # "GIT_SSL_CAINFO=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
        # "SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
      ];
    };

    fakeRootCommands = ''
      mkdir -p ./tmp ./lib64 ./usr/bin ./root/static ./etc
      echo "ID=nixos" > ./etc/os-release
      cp ./bin/env ./usr/bin/

      # Copy static assets to /root so that make-site.sh can find them
      mkdir -p ./root/static/ttf/ ./root/css/
      cp -Lrv --no-preserve=mode ${pkgs.nodePackages.katex}/lib/node_modules/katex/dist/{katex.min.css,fonts} ./root/css/;
      cp -Lrv --no-preserve=mode ${pkgs.julia-mono}/share/fonts/truetype/JuliaMono-Regular.ttf ./root/static/ttf/julia-mono.ttf

      # Needed for Github Actions
      # ln -s ''${pkgs.glibc}/lib/ld-linux-x86-64.so.2 ./lib64/ld-linux-x86-64.so.2
      # ln -sf ''${pkgs.gnutar}/bin/tar ./bin/tar
    '';
  }
