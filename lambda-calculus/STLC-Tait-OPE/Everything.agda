{-
  Normalization theorem for the Simply Typed Lambda-Calculus:

    "every typable term is normalizable".

  Based on

    Thierry Coquand and Peter Dybjer. 1997.
    Intuitionistic model constructions and normalization proofs.
    Mathematical. Structures in Comp. Sci. 7, 1 (February 1997), 75-94.
    DOI=10.1017/S0960129596002150 http://dx.doi.org/10.1017/S0960129596002150 

  and

    Thorsten Altenkirch and James Chapman. 2009.
    Big-step normalisation.
    J. Funct. Program. 19, 3-4 (July 2009), 311-333.
    DOI=10.1017/S0956796809007278 http://dx.doi.org/10.1017/S0956796809007278 

  The idea to use OPEs (order-preserving embeddings) has been put forward in

    James Chapman. 2009. Type Checking and Normalization.
    Ph.D. thesis, School of Computer Science, University of Nottingham.

  and

    Andreas Abel and James Chapman. 2014.
    Normalization by evaluation in the delay monad: A case study for
    coinduction via copatterns and sized types.
    In MSFP'14, volume 153 of EPTCS, pages 51--67.
    http://arxiv.org/abs/1406.2059v1
-}

module STLC-Tait-OPE.Everything where

import STLC-Tait-OPE.Util
import STLC-Tait-OPE.Syntax
import STLC-Tait-OPE.Recursive
import STLC-Tait-OPE.StrongComputability
import STLC-Tait-OPE.StructurallyRecursive
import STLC-Tait-OPE.Sound
