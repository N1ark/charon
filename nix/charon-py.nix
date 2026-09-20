{ charon
, python3
, runCommand
}:
let
  charon-py-tests = runCommand "charon-py-tests"
    {
      buildInputs = [ python3 ];
      # Tell the tests where to find the llbc files.
      CHARON_TESTS_DIR = "${charon}/tests-llbc";
    } ''
    cp -r ${./../charon-py} charon-py
    chmod -R u+w charon-py
    cd charon-py
    python3 -m unittest discover -s tests -v
    touch $out
  '';
in
{ inherit charon-py-tests; }
