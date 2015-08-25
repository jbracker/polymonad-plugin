

all:
	[ -f ./cabal.sandbox.config ] \
		|| [ -d ./.cabal-sandbox ] \
		|| cabal sandbox init
	cabal install