# Verith
Verith (VERIfied aRITHmetic) is a Coq library that proves 
several results about native-integer arithmetic. It enables 
users to write safe programs that make use of native integers
without dealing with the complex, ceremonial and low-level 
manipulations usually required by the certification of such
programs.
Verith is intended to be used in combination with the
[extraction mechanism](https://coq.inria.fr/refman/addendum/extraction.html) 
to help certifying programs in compiled languages.

It has no dependencies except than the Coq standard library
and uses no axiom other than those provided by Coq itself.

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
