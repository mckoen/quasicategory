# Functor quasi-categories in Lean 4

This repository contains a completely formalized proof that the internal hom between a simplicial set and a quasi-category is a quasi-category ([0066](https://kerodon.net/tag/0066)).

The main result is in [Quasicategory/QCat.lean](Quasicategory/QCat.lean), where it is used to show the category of quasi-categories is enriched over itself.

Code in [Quasicategory/TopCatModelCategory](Quasicategory/TopCatModelCategory/) is taken from [Joël Riou](https://github.com/joelriou)'s repository [topcat-model-category](https://github.com/joelriou/topcat-model-category). Everything else is authored by me.