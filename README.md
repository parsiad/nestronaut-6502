# nestronaut-6502

This project is an emulator for the [MOS 6502 processor](https://en.wikipedia.org/wiki/MOS_Technology_6502), implemented in Rust.
It includes a comprehensive test suite to verify correct execution of 6502 instructions.

This emulator is specifically intended as part of a [Nintendo Entertainment System](https://en.wikipedia.org/wiki/Nintendo_Entertainment_System) (NES) emulator, which means it follows the behavior of the [Ricoh 2A03](https://en.wikipedia.org/wiki/Ricoh_2A03) variant of the 6502.
Notably, BCD (Binary-Coded Decimal) mode is not supported, as the Ricoh 2A03 does not implement it.

## Example Usage

```rust
let mut cpu = CPU::new();
cpu.load_and_run(&[
  0xA9, 0x42, // LDA #$42,
  0x00 // BRK
]);
```

## Snake Game

The snake game from [Easy 6502](https://skilldrick.github.io/easy6502/#snake) can be run with

```
cargo run snake
```

The SDL code for rendering the game is from [Writing NES Emulator in Rust](https://bugzmanov.github.io/nes_ebook/chapter_3_4.html).

![](https://bugzmanov.github.io/nes_ebook/images/ch3/snk_game.gif)
