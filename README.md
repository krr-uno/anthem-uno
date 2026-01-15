# anthem-uno

This is an extension of the `anthem` 2.0 release that is currently being developed by the NLPKR lab at the University of Nebraska Omaha.
`anthem` is a command-line application for assisting in the verification of answer set programs.
It operates by translating answer set programs written in the mini-gringo dialect of [clingo](https://potassco.org/clingo/) into many-sorted first-order theories.
Using automated theorem provers, `anthem` can then verify properties of the original programs, such as strong and external equivalence.

Check out the [Manual](https://potassco.org/anthem/) to learn how to install and use `anthem`.

If you want to use `anthem` as a library to build your own application, you can do so.
Check out the [API documentation](https://docs.rs/anthem/) for the available functionalities.

## Examples
Examples of verification problems are grouped by equivalence (strong or external) within the [res/examples](res/examples) directory.
For example, visit the [cover](res/examples/external_equivalence/cover) directory for instructions on how to compare a program solving the Exact Cover problem [cover.1.lp](res/examples/external_equivalence/cover/cover.1.lp) against a first-order specification [cover.spec](res/examples/external_equivalence/cover/cover.spec).

## Vampire
The 2.0 release of `anthem` and the associated [paper](https://arxiv.org/abs/2507.11704) used `vampire` v4.9casc2024 linked with Z3, found [here](https://github.com/vprover/vampire/releases/tag/v4.9casc2024).
To replicate this setup, build `vampire` from source using `git clone --recursive` to include the Z3 files. 
Build Z3 before `vampire`. 

## License

`anthem` is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details!

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in `anthem` by you shall be licensed as above, without any additional terms or conditions.
