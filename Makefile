

install: init
	cabal install

clean: init
	cabal clean

doc: init
	cabal configure && cabal haddock

opendoc:
	xdg-open ./dist/doc/html/polymonad-plugin/index.html 

init:
	[ -f ./cabal.sandbox.config ] || [ -d ./.cabal-sandbox ] || cabal sandbox init
	