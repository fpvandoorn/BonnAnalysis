# Collaborative Analysis Formalisation seminar
For the course at Bonn SuSe 24.

* We will use a private channel on the [Lean Zulip](https://leanprover.zulipchat.com/) to coordinate.
* [Blueprint](http://florisvandoorn.com/BonnAnalysis/blueprint/)
* [Blueprint as pdf](http://florisvandoorn.com/BonnAnalysis/blueprint.pdf)
* [Doc pages for this repository](http://florisvandoorn.com/BonnAnalysis/docs/)

## Installation

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

* You have to install Lean, and two supporting programs: Git and VSCode. Follow these [instructions](https://leanprover-community.github.io/get_started.html) to do this. You do not have to follow the last step (creating Lean projects). Instead, use either VSCode or a terminal to get this repository.

### Get the Repository using VSCode

* Open Visual Studio Code
* Press `Clone Git Repository` (if you don't see the welcome screen, you can press `ctrl+shift+P` (or `cmd+shift+P` on Mac), type `Git: Clone` and press `enter`)
* Type `https://github.com/fpvandoorn/BonnAnalysis.git` and press enter
![1](img/ss1.png)

* Choose a folder where you want to clone this repository (everything will be placed in a subfolder `BonnAnalysis`).
* Press `open` when asked if you want to open the cloned repository
* Open the file `BonnAnalysis/Test.lean` using the explorer button in the top-right. Do **not** press `Restart Lean` or `Rebuild Imports` when these pop-ups show up. (If you do, you will rebuild mathlib yourself, which is not recommended)

![2](img/ss2.png)
* In the top-middle (or top-right) of the screen there is a Lean menu marked by `∀`.
  In it, choose `Project Actions... > Project: Fetch Mathlib Build Cache`.
  This downloads mathlib, and will take a bit of time.

![3](img/ss3.png)

* Once this is finished, press the `Rebuild Imports` button. The file should be ready a few seconds later. If you see a blue squiggle under `#eval`, Lean is running correctly.


### Get the Repository using a terminal

* Open a terminal (I recommend `git bash` on Windows, which was installed as part of git in the first step).

* Use `cd` to navigate to a directory where you would like to create the `BonnAnalysis` folder.

* Run `git clone https://github.com/fpvandoorn/BonnAnalysis.git`.

* Run `cd BonnAnalysis`

* Run `lake exe cache get!`
  * This downloads mathlib, and will take a bit of time
  * On Windows, if you get an error that starts with `curl: (35) schannel: next InitializeSecurityContext failed` it is probably your antivirus program that doesn't like that we're downloading many files. The easiest solution is to temporarily disable your antivirus program.

* Launch VS Code, either through your application menu or by typing
  `code .` (note the dot!). (MacOS users need to take a one-off
  [extra step](https://code.visualstudio.com/docs/setup/mac#_launching-from-the-command-line)
   to be able to launch VS Code from the command line.)

* If you launched VS Code from a menu, on the main screen, or in the File menu,
  click "Open folder" (just "Open" on a Mac), and choose the folder
  `BonnAnalysis` (*not* one of its subfolders).

* Test that everything is working by opening `BonnAnalysis/Test.lean`.
  It is normal if it takes 10-60 seconds for Lean to start up.

## Building the blueprint

To test the Blueprint locally, you can compile `print.tex` using XeLaTeX (i.e. `xelatex print.tex` in the folder `blueprint/src`). If you have the Python package `invoke` you can also run `inv bp`.
If you feel adventurous and want to build the web version of the blueprint locally, you need to install some packages by following the instructions [here](https://pypi.org/project/leanblueprint/). But if the pdf builds locally, you can just make a pull request and use the online blueprint.

## Making a pull request

* Update this repository to the latest version (run `git pull` or `git fetch` + `git merge` or their equivalents using VSCode source control).

* Switch to a branch. You can create a new branch using `git switch -c mynewbranch` or use `... > Checkout to > Create new branch` in VSCode. (This can also be done after the next step if you forget.)

* Write some Lean code
  - Try to follow the style guide: https://leanprover-community.github.io/contribute/style.html
  - Make sure it compiles

* Push your branch to your fork of this repository
  - Using the terminal you first have to create a fork on Github and use `git remote add` to add this fork
  - Using VSCode this fork automatically created for you
  - When you have added a new file, please import it in `BonnAnalysis.lean`.

* Open a pull request
  - Just after you push [this page](https://github.com/fpvandoorn/BonnAnalysis) will have a message on the top prompting you to open a pull request.

* If it builds, I'll merge it.
  - Feel free to make a pull request with partial work and a lot of sorry's, as long as it builds.

Reminder: Some additional details can be found in the instructions of the LeanCourse repository: https://github.com/fpvandoorn/LeanCourse23/blob/master/LeanCourse/Project/README.md