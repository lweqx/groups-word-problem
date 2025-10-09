{
  rocqPackages,
  version ? null,
}:

let
  inherit (rocqPackages) rocq-core mkRocqDerivation lib;
in
mkRocqDerivation {
  pname = "coq-library-undecidability";
  repo = "coq-library-undecidability";
  owner = "uds-psl";

  inherit version;
  defaultVersion = lib.switch rocq-core.rocq-version [
    {
      case = "9.0";
      out = "rocq-9.0";
    }
  ] null;
  release = {
    "rocq-9.0".sha256 = "sha256-v82jbE5iqlinMwuyfw699lHVkIRO25xZTfU2/LrqwwA=";
  };

  propagatedBuildInputs = [
    rocqPackages.stdlib
  ];

  meta = {
    homepage = "https://github.com/uds-psl/coq-library-undecidability";
    description = "Coq Library of Undecidability Proofs";
    maintainers = with lib.maintainers; [
      #lweqx
    ];
    license = lib.licenses.mpl20;
  };
}
