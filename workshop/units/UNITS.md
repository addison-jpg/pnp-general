# Tiny repo units: a manifest

Each unit is a folder group that could become its own small repo (a fork later, when GitHub access works). A unit names its folders and what it depends on. Nothing is moved yet.

| unit | folders | depends on |
|---|---|---|
| core | core/ | none |
| asteroid | asteroid/ | none |
| bus | workshop/bus/, workshop/route/ | asteroid |
| board | boards/, workshop/board/, workshop/board_formal/ | asteroid |
| clusters | workshop/cluster/ | asteroid |
| formal-physics | physics/ | asteroid |
| formal-math | math/ | asteroid |
| culture | culture/ | core |
| philosophy | philosophy/ | core |
| workshop-misc | workshop/ (the rest) | all of the above |

## Not claimed

- That this split is final. It is a first manifest for review.
- That a unit can be merged without conflict. Merging is the step that needs checking.
