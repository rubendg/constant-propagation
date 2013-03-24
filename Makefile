CABAL-CONFIGURE-FLAGS := --user
CABAL-BUILD-FLAGS     :=

all : haskell

src/JS/AG.hs : src/JS/AG.ag src/JS/AG/Base.ag src/JS/AG/Flow.ag src/JS/AG/AvailableVariables.ag src/JS/AG/Folding.ag src/JS/AG/Desugaring.ag
	uuagc -Hdcfwsv --self -P src/JS src/JS/AG.ag

haskell : src/JS/AG.hs
	runhaskell Setup.hs configure $(CABAL-CONFIGURE-FLAGS) --ghc-options=-XStandaloneDeriving --ghc-options=-XTypeSynonymInstances --ghc-options=-XTypeSynonymInstances
	runhaskell Setup.hs build $(CABAL-BUILD-FLAGS)

example :
	@cat examples/small | ./dist/build/jssoft/jssoft.exe cfg
	
runtests :
	@./dist/build/unittest/unittest

report:
	lhs2TeX -o report.tex report.lhs
	pdflatex report.tex
	rm -f report.aux report.ptb report.log report.tex

clean:
	rm -rf dist out.* \
  rm src/JS/AG.hs

.PHONY : haskell
