# Lean package with a Mathlib dependency (template repository)

This sets up a basic Lean package with a Mathlib dependency. If you first need to install Lean 4, you can do so by following the instructions on this basic [Lean Package](https://github.com/matematiflo/LeanPackage) template repository.

## Install instructions

### Clone the repo

Clone the present repository.

```script
https://github.com/matematiflo/MathlibPackage.git
```

### Download the compiled Mathlib files

> For the following step, it might be better to not use the terminal from within VS Code (which might generate error messages until the binaries have ben downloaded).

From a terminal, run the command line

```script
lake exe cache get
```

This downloads the compiled Mathlib files, so you can avoid building Mathlib locally (which takes a long time). In principle, though, this can also be done automatically via the command `lake build`.

### Go to the test file

Go to the file [MathlibTest.lean](MathlibTest.lean) and check that there are no error messages (the file imports the file `Mathlib.Algebra.Group.Defs` of the Mathlib library, which should only take a few seconds).

```lean
import Mathlib.Algebra.Group.Defs

example [Group G] : (∀ g : G, 1 * g = g) := by intro g; exact one_mul g
```

When you position your cursor at the end of the first `example` line (for instance immediately after the `by intro g; exact one_mul g`), you should see the following message in the Lean Infoview panel (which in principle opens automatically to the right).

> **No goals**

This example gives a proof (taken from Mathlib) that, in a group `G`, the neutral element `1` satisfies, for all `g` in `G`, `1 * g = g` :-)

The other four examples are just different ways of writing a proof that `1 + 1 = 2`. Again, it holds by definition.

## Troubleshooting and updating

If you get error messages when parsing `MathlibTest.lean`, or if you want to update Mathlib, run the following three commands (one after the other).

```script
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe cache get
```

Then close the file `MathlibTest.lean` and open it again.

## Codespaces

If you wish to work on this project online and without installing anything, you can do so by opening a Codespace. Just follow the link below and click on `Create new codespace` (**GitHub account required**).

[![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://github.com/codespaces/new/matematiflo/MathlibDependency)
  
Alternately, you can open a Codespace by clicking on the [Code button](https://github.com/matematiflo/MathlibDependency) of the current repository (possibly slower, though).

If you commit any modified file from within your Codespace, the repo will be forked to your GitHub account and your work will be saved there.

To leave a Codespace, it is recommended that you stop it before closing the browser window:

1. Click on your Codespace name at the bottom-left of the VS Code interface.
2. Choose `Stop current Codespace` from the list of options.
3. Wait until the Codespace has stopped to close your browser tab.

To access a Codespace that you have previously created, just go to

> [https://github.com/codespaces](https://github.com/codespaces)

or launch them directly from the Code button of the relevant repository (no setup required this time!).
