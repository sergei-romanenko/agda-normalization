# Combinatory calculus

##Normalization Theorem for the Simply Typed Combinators (1)

* GaspesSmith-STCC-SK

A proof of the fact that

> "Every typable term is normalizable".

  The original proof (in Alf) was presented in

* Veronica Gaspes and Jan M. Smith. 1992.
**Machine checked normalization proofs for typed combinator calculi.**
In *Proceedings of the Workshop on Types for Proofs and Programs*,
pages 177-192, Båstad, Sweden.

The Agda version was written by Wojciech Jedynak
    <https://github.com/wjzz/Agda-small-developments-and-examples>
and modified by Sergei Romanenko.

## Normalization theorem for the Simply Typed Combinators (2)

* STCC-SK-norm
* STCC-SK-red
* STCC-SK-solver

and

* STCC-SystemT-norm
* STCC-SystemT-red
* STCC-SystemT-solver

Based on

* Thierry Coquand and Peter Dybjer. 1997.
**Intuitionistic model constructions and normalization proofs.**
*Mathematical. Structures in Comp. Sci. 7, 1 (February 1997)*, 75-94.
DOI=10.1017/S0960129596002150 <http://dx.doi.org/10.1017/S0960129596002150>

* Peter Dybjer and Andrzej Filinski. 2000.
**Normalization and Partial Evaluation.**
In *Applied Semantics, International Summer School, APPSEM 2000, Caminha,
Portugal, September 9-15, 2000, Advanced Lectures*,
Gilles Barthe, Peter Dybjer, Luis Pinto, and João Saraiva (Eds.).
Springer-Verlag, London, UK, UK, 137-192.

## Tait in one big step (using the Bove-Capretta technique)

* STCC-Tait-SK
* STCC-Tait-SystemT

Based on

* Ana Bove and Venanzio Capretta. 2001.
**Nested General Recursion and Partiality in Type Theory.**
In *Proceedings of the 14th International Conference on Theorem Proving
in Higher Order Logics (TPHOLs '01)*,
Richard J. Boulton and Paul B. Jackson (Eds.).
Springer-Verlag, London, UK, UK, 121-135. 

* Thorsten Altenkirch and James Chapman. 2006.
**Tait in one big step.**
In *Proceedings of the 2006 international conference on Mathematically
Structured Functional Programming (MSFP'06)*,
Conor McBride and Tarmo Uustalu (Eds.).
British Computer Society, Swinton, UK, UK, 4-4.

## Normalization by evaluation in the delay monad

* STCC-Delay-SK-norm
* STCC-Delay-SK-red

Based on

* Thierry Coquand and Peter Dybjer. 1997.
**Intuitionistic model constructions and normalization proofs.**
*Mathematical. Structures in Comp. Sci. 7, 1 (February 1997)*, 75-94.
DOI=10.1017/S0960129596002150 <http://dx.doi.org/10.1017/S0960129596002150>

* Peter Dybjer and Andrzej Filinski. 2000.
**Normalization and Partial Evaluation.**
In *Applied Semantics, International Summer School, APPSEM 2000, Caminha,
Portugal, September 9-15, 2000, Advanced Lectures*,
Gilles Barthe, Peter Dybjer, Luis Pinto, and João Saraiva (Eds.).
Springer-Verlag, London, UK, UK, 137-192.

* Andreas Abel and James Chapman. 2014.
**Normalization by evaluation in the delay monad: A case study for
coinduction via copatterns and sized types.**
In MSFP'14, volume 153 of EPTCS, pages 51--67.
<http://arxiv.org/abs/1406.2059v1>
