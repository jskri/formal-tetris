# Tetris, proved correct in Rocq

Tetris specified and proved correct in Rocq, with independent LLM-generated Rust and JavaScript implementations. Implementations are themselves informally proved, and tested, to refine the Rocq model.

![A screenshot of the multiplayer game](img/tetris.png)


## Why

The usual approach to software treats the code as the source of truth. Here it is the other way around: the *model* is the source, and the code is derived from it, the way a binary is derived from source by a compiler. The model is written in Rocq, its invariants are machine-checked there, and the code is generated from the model together with a target-language-specific skill (see [github.com/jskri/rocq-to-code-skills](https://github.com/jskri/rocq-to-code-skills)), an implementation document (`implementation.md`, fixing every decision the model leaves open), and a refinement proof (`proofs.md`, arguing that the code is a faithful image of the model). The refinement proof is the one part of this chain that is not machine-checked: it is generated and must be checked by a human, which is why differential tests against an oracle derived from the model exist as a backstop.

The full reasoning behind this approach, including what is machine-checked and what is not, can be found at [github.com/jskri/model-as-source-development](https://github.com/jskri/model-as-source-development).

## Models

The models address the logical core of the game, not I/O or rendering. They are organized as a tower of refinements. Each model adds a feature on top of the previous one and is proved to refine it. Requirements are tracked in `definitions_requirements.md`, a hierarchical tree where each requirement has an id (`req-*`); models reference these ids for the requirements they address.

**T1**, core mechanics: piece movement, rotation, falling, fixing, line clearing, gameover. The main grid and pieces are unified under the notion of grid. A small grid algebra (union, intersection, translation, inclusion) allows one to express main operations. This model addresses `req-flow`, `req-piece-ctrl`, `req-piece-loc`, `req-piece-free`, `req-piece-init`, `req-piece-move-dir`, `req-piece-move-def`, `req-piece-rot`, `req-piece-fall`, `req-piece-fix`, `req-piece-fix-gameover`, `req-piece-fix-new`, `req-grid-init`, `req-grid-clear`.

**T2**, refines T1 with score, level and combo. Addresses `req-score`, `req-score-init`, `req-score-formula`, `req-level`, `req-level-init`, `req-level-formula`.

**T3**, refines T2 with the hold mechanics (swapping the current piece with a held piece). Addresses `req-hold`, `req-hold-swap`, `req-hold-empty`, `req-hold-limit`.

**T4**, refines T3 with the next pieces preview mechanics (drawing next pieces from a bag randomizer and presenting them). Addresses `req-preview-len`, `req-preview-init`, `req-preview-pop`.

**T5**, refines T4 with the piece drop mechanics (dropping the current piece instantly). Addresses `req-piece-drop`, `req-piece-shadow`.

**T6**, refines T5 with the wall kick mechanics (offsetting a piece from an obstacle when it prevents rotation). Addresses `req-piece-kick`.

**T7**, refines T6 with the multi-player mode (sending garbage to opponents when clearing lines). Addresses `req-multi`, `req-multi-succ`, `req-multi-target-nonself`, `req-multi-garbage-gen`, `req-multi-garbage-cancel`, `req-multi-garbage-send`, `req-multi-garbage-materialize`, `req-multi-gameover`.

Each model Tx is in a file `Tx.v`. Proofs of state invariants and step invariants are in a file `TxProofs.v`, together with a proof that Tx refines Tx-1 (T1 has no predecessor to refine).

Proof status: All proved (but T7's step invariants and refinement are not yet formulated).


## Checking the proofs

Tested with Rocq 9.1.0, dune 3.19.1, coq-hammer-tactics 1.3.2+9.1. The `hammer` tactic is not actually invoked by any proof in this repo, so no external ATP is required.

```bash
dune build
```

This type-checks every `.v` file; if it succeeds, every theorem (in particular the invariant and refinement proofs) is machine-checked.

Alternatively, if you want an empty output on success:

```sh
dune build --display=progress --action-stdout-on-success=swallow --action-stderr-on-success=must-be-empty
```

The proofs can also be stepped through interactively in an editor. VSCode (tested with 1.124.0) picks up the project layout via `_CoqProject`.

See also the [Using the CI image locally](#using-the-ci-image-locally) below.


## Implementations

Each model Tx has an implementation in the directory `<lang>/<model>/`, where `<lang>` is in `{rs, js}` and `<model>` is in `{t1, t2, t3, t4, t5, t6, t7}`. The file layout is largely the same for both languages:

- `implementation.md` details the implementation choices.

- `proofs.md` informally proves that the code refines the Tx model.

- `model.<lang>` implements Tx: one function for the Tx module and Tx's `State` encapsulated in a `Machine` class.

- `view.<lang>` renders a `Machine` object.

- `main.rs`/`controller.js` instantiates a `Machine` object, dispatches events to the right methods, controls time and randomness, and performs rendering.

- `instance.<lang>` defines concrete values for Tx's parameters.

- `tests/` contains unit tests, property-based tests, fuzz tests, and an oracle.

An additional `<lang>/tfinal/` implementation of `T7.v` adds to `<lang>/t7/`: sounds, clear-line/game-over animations, and a local hall of fame.

Each implementation builds upon the previous ones: `t7/` upon `t6/`, and so on.

Rust implementations work on Linux, macOS and Windows. They mainly rely on macroquad (rendering, main loop), gilrs (gamepad), and rodio (sound).

JavaScript implementations rely on standard Web APIs: Canvas, Web audio, Gamepad, WebRTC.


## Running the tests

### Rust

```bash
cd rs/ && cargo test
```

### JavaScript

```bash
cd js/ && npm install && npm test
```

Tested with npm 11.17.0 and node v24.19.0.

See also [Using the CI image locally](#using-the-ci-image-locally) below.


## Using the CI image locally

You can run `check-proofs-run-tests.sh` to check proofs and run implementation tests locally, using the CI image.

**Warning**: This script changes file ownership to rocq. This is needed only if your id/group is *not* `1000:1000`; otherwise comment out the corresponding step. Also note that the file ownership "restoration" forces `$(id -u):$(id -g)`, which may change the original owner, so use it with care.


## Running the game

### Rust

```bash
cd rs/ && cargo run -r --bin tfinal # or `--bin tx` for a previous version, with `x` in 1-7
```

### JavaScript

1. Start a local HTTP server:

```bash
cd js/ && npx serve -l 8000  # or `python3 -m http.server -b 127.0.0.1 8000` for instance
```

2. Open `http://127.0.0.1:8000/tfinal/` in a browser (or `http://127.0.0.1:8000/tx/` for a previous version, with `x` in 1-7).

**Note**: Be sure to include the trailing slash.


## Multiplayer mode

`t7/` and `tfinal/` implement a multiplayer mode.

**Warning**: A large part of the communication protocol, especially the Rust one, is outside the scope of `T7.v` and has, to a significant extent, been designed by an LLM. As a result, and as long as it has not been properly modeled, it is expected to be buggy. Moreover, it has not been tested exhaustively, mainly on a local network setup with Linux/macOS machines. Finally, be aware that network communication may fail if at least one player is behind a NAT. The code currently uses a STUN (Session Traversal Utilities for NAT) server, `stun:stun.l.google.com:19302`, but no TURN (Traversal Using Relays around NAT) server, for cost reasons.

In multiplayer mode, one player must host the game, and others must join. A joiner must send the host a generated code through an external channel of their choice. For each joiner, the host adds a connection using that code and generates a code that must be sent back to the joiner. Once the codes have been exchanged, the game can start.

**Note**: Cross-play between the Rust and JavaScript implementations is not possible at the moment, since they use different protocols (custom for Rust vs. WebRTC for JavaScript).


## Input

| Action                         | Keyboard    | Gamepad     |
|--------------------------------|-------------|-------------|
| move piece left                | left arrow  | left d-pad  |
| move piece right               | right arrow | right d-pad |
| move piece down                | down arrow  | down d-pad  |
| drop piece                     | up arrow    | up d-pad    |
| rotate piece clockwise         | x           | button 1    |
| rotate piece counter-clockwise | z           | button 0    |
| hold piece                     | space       | button 3    |

No separate configuration file exists at the moment. To change the input, modify directly the sources:

- in Rust, edit `fn key` / `fn gamepad_button`. These are defined once, in the `src/misc.rs` of the earliest model that introduces them (`t1`, `t3`, or `t5`, depending on which actions that model adds); later models import or re-export that same definition rather than redefining it, so edit it at its source.

- in JavaScript, edit `KEYMAP`/`GAMEPAD_MAP` in the corresponding `controller.js`.



## File tree

```
.
├── dune-project
├── dune
├── _CoqProject
├── README.md
├── img
│   └── tetris.png
├── LICENSE
├── ci
│   ├── Dockerfile
│   └── VERSION
├── .github
│   └── workflows
│       └── ci.yml
├── check-proofs-run-tests.sh
├── definitions_requirements.md
├── T1.v
├── T1Proofs.v
├── T2.v
├── T2Proofs.v
├── T3.v
├── T3Proofs.v
├── T4.v
├── T4Proofs.v
├── T5.v
├── T5Proofs.v
├── T6.v
├── T6Proofs.v
├── T7.v
├── T7Proofs.v
├── Notations.v
├── QuantifiersProofs.v
├── Quantifiers.v
├── rs
│   ├── assets
│   │   ├── JetBrainsMono-Regular.ttf
│   │   ├── OFL.txt
│   │   └── tetris.svg
│   ├── Cargo.lock
│   ├── Cargo.toml
│   ├── install-desktop-icon.sh
│   ├── t1
│   │   ├── Cargo.lock
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── misc.rs
│   │   │   ├── model.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── oracle.rs
│   │       └── test_instance.rs
│   ├── t2
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── model.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── oracle.rs
│   │       └── test_instance.rs
│   ├── t3
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── misc.rs
│   │   │   ├── model.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── oracle.rs
│   │       └── test_instance.rs
│   ├── t4
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── model.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── oracle.rs
│   │       └── test_instance.rs
│   ├── t5
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── misc.rs
│   │   │   ├── model.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── oracle.rs
│   │       └── test_instance.rs
│   ├── t6
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── misc.rs
│   │   │   ├── model.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── oracle.rs
│   │       └── test_instance.rs
│   ├── t7
│   │   ├── Cargo.toml
│   │   ├── implementation.md
│   │   ├── proofs.md
│   │   ├── src
│   │   │   ├── app.rs
│   │   │   ├── instance.rs
│   │   │   ├── lib.rs
│   │   │   ├── main.rs
│   │   │   ├── misc.rs
│   │   │   ├── model.rs
│   │   │   ├── net.rs
│   │   │   ├── session.rs
│   │   │   ├── text.rs
│   │   │   └── view.rs
│   │   └── tests
│   │       ├── model_fuzz_test.rs
│   │       ├── model_properties_test.rs
│   │       ├── model_unit_test.rs
│   │       ├── net_unit_test.rs
│   │       ├── oracle.rs
│   │       ├── session_integration_test.rs
│   │       └── test_instance.rs
│   └── tfinal
│       ├── Cargo.toml
│       ├── implementation.md
│       ├── proofs.md
│       └── src
│           ├── anim.rs
│           ├── highscores.rs
│           ├── main.rs
│           └── sound.rs
└── js
    ├── package.json
    ├── package-lock.json
    ├── test-runner.js
    ├── lib
    │   └── utils.js
    ├── vendor
    │   └── fflate.js
    ├── t1
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    ├── t2
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    ├── t3
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    ├── t4
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    ├── t5
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    ├── t6
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    ├── t7
    │   ├── implementation.md
    │   ├── proofs.md
    │   ├── model.js
    │   ├── view.js
    │   ├── controller.js
    │   ├── instance.js
    │   ├── index.html
    │   └── tests
    │       ├── model.fuzz.test.js
    │       ├── model.properties.test.js
    │       ├── model.unit.test.js
    │       ├── oracle.js
    │       └── testInstance.js
    └── tfinal
        ├── controller.js
        ├── highscores.js
        ├── implementation.md
        ├── index.html
        ├── instance.js
        ├── proofs.md
        ├── sound.js
        ├── sp_controller.js
        └── view.js
```


## License

MIT.

