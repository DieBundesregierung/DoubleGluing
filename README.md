This repository contains artifacts accompanying the paper **A Formalization of the Double Gluing Construction in UniMath**. This work will eventually be incorporated into the UniMath library.

Installation:
- Install the [UniMath library](https://github.com/UniMath/UniMath). Install instructions can be found [here](https://github.com/UniMath/UniMath/blob/master/documentation/setup/Install.md) .
- clone this repository
- execute the following commands at the location of the _CoqProject file:
  - $ coq_makefile -f _CoqProject -o Makefile
  - $ make

Documentation:
- preliminaries.v  contains results about symmetric monoidal closed categories as described in section 3.2 of the paper.
- double_pullbacks.v  contains the theory of <em>double pullbacks</em> as presented in section 3.3 of the paper.
- natural_contraction.v  contains the definition of <em>natural contractions</em> as defined during section 4 of the paper.
- double_gluing/double_gluing.v  contains the definition of the double-glued category obtained from the general double gluing construction as found in the beginning of section 4 of the paper.
- double_gluing/monoidal  contains files defining the symmetric monoidal structure of the double glued category as defined during section 4. In particular the file symmetry.v contains the (displayed) symmetric structure, that the other files work towards to.
- double_gluing/closed  contains files defining the closedness structure for the symmetric monoidal double glued category. In particular the file closed.v contains the bundled symmetric monoidal closed double-glued category that the other files work towards to.
- double_gluing/linear_cat  contains files defining the bang-exponential as a comonad and the linear structure of the double-glued category. In particular the file contains the bundled linear double-glued category that this whole project works towards to.

- double_gluing/linear_cat/linear_cat.v  is the main result of this project. It depends on all other files.
