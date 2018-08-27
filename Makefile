
all:
	ghc --make -rtsopts rungame.hs
	ghc --make -rtsopts rungameA.hs
	ghc --make -rtsopts -prof -fprof-auto -osuf p_o -hisuf p_hi rungame.hs
	ghc --make -rtsopts -prof -fprof-auto -osuf p_o -hisuf p_hi rungameA.hs
    
opt:
	ghc --make -rtsopts -O3 -fforce-recomp rungame.hs
	ghc --make -rtsopts -O3 -fforce-recomp rungameA.hs
    
ostari:
	ghc --make -rtsopts -prof -fprof-auto rungameA.hs
    
baltag:
	ghc --make -rtsopts -prof -fprof-auto rungame.hs