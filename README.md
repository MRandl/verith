# Verith
Verith (VERIfied aRITHmetic) is a Coq library that proves 
several results about native-integer arithmetic. It enables 
users to write safe programs that make use of native integers
without dealing with the complex, ceremonial and low-level 
manipulations usually required by the certification of such
programs.
Verith is intended to be used in combination with the
[extraction mechanism](https://coq.inria.fr/refman/addendum/extraction.html) 
to help certifying programs in OCaml. It can also be used as is for regular
Coq programs.

It has no dependencies other than the Coq standard library
and does not rely any axiom except for those provided by Coq itself.

# License
This library is licensed under the MIT License.
See [the license](LICENSE) for more details.
The license takes precedence over any comment and/or description
provided in this project.

# Install
```
git clone git@github.com:MRandl/verith
cd verith
make
```
Note that this assumes coqc and coq-makefile to be accessible on PATH.
