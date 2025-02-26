Contains:
- A reduction from ground temporal planning (abstract) to a diagonal timed automaton
  - Verified (not executable):
    - Follows: https://ojs.aaai.org/index.php/AAAI/article/view/6539 by Gigante, Micheli, Montanari, Scala
    - Currently does not check
    - Adds some things which the original authors added in https://www.sciencedirect.com/science/article/pii/S0004370222000261
  - Executable (unverified)
    - Follows: https://www.sciencedirect.com/science/article/pii/S0004370222000261
    - Adds some ideas from: https://ojs.aaai.org/index.php/AAAI/article/view/6539
- An abstract formulation of temporal propositional planning semantics (based on work by Abdulaziz, Kurz, Lammich; https://arxiv.org/abs/2203.13604) to enable the formalisation.
  - Also https://www.semanticscholar.org/paper/PDDL2.1%3A-An-Extension-to-PDDL-for-Expressing-Fox-Long/
  - And https://ojs.aaai.org/index.php/AAAI/article/view/6539
- A reduction from ground temporal planning (pretty-printed in a PDDL-like format; based on work by Abdulaziz, Kurz, Lammich; https://arxiv.org/abs/2203.13604) to networks timed automata (in `.muntax`; by Simon Wimmer; https://github.com/wimmers/munta; https://link.springer.com/chapter/10.1007/978-3-030-45190-5_24)
  - Follows the structure of: https://ojs.aaai.org/index.php/ICAPS/article/view/3476 by Bogomolov, Greitschus, Heinz, Maggazeni, Podelski, Wehrle
  - Adds ideas from https://www.sciencedirect.com/science/article/pii/S0004370222000261
  - Executable but unverified
- An concrete formulation of temporal propositional planning syntax (based on work by Abdulaziz, Kurz, Lammich; https://arxiv.org/abs/2203.13604) to enable the formalisation.

Very much work in progress and not formally verified yet.
