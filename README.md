Verifying Higher-order Contracts with Why3
=============================================================

This is class project for 838G, exploring the approach of verifying higher-order contracts
by straightforward compilation to WhyML, which gets verified by Why3.

To run this project, you need to have installed:
* [Racket](https://download.racket-lang.org/)
* [The Why3 platform](http://why3.lri.fr/#download)
* [Alt-Ergo](https://alt-ergo.ocamlpro.com/index.php#releases) (recommended)
* [Z3](https://z3.codeplex.com/releases) (recommended)

### How to run this project

#### Set up Why3

* After downloading and installing Why3 and the theorem provers, run `why3 config --detect`

#### Set up this project

* Make sure Racket is in your path
* Clone this repository
* Compile this project:
```{bash}
cd path-to-this-project/src
raco link .
raco make cmdline.rkt
```

* File `test/examples.rkt` contains examples. To compile it to `examples.mlw`, run:

```{bash}
racket cmdline.rkt test/examples.rkt test/examples.mlw
```

* You can open the WhyML file `examples.mlw` with Why3's ide:

```{bash}
why3 ide test/examples.mlw
```

* To verify the file using `Z3`, click `Z3` button on the left panel.
  If there are some goals left unverified, you can try with another prover,
  such as `Alt-Ergo`.


