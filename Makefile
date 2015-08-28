
SandboxExists = [ -f ./cabal.sandbox.config ] || [ -d ./.cabal-sandbox ]

all:
	$(SandboxExists) || cabal sandbox init
	cabal install

clean:
	cabal clean