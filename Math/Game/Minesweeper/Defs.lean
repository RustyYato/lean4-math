import Math.Type.Notation
import Math.Data.Vector.Defs
import Math.Data.Nat.Basic

structure MinsweeperData (n m: ℕ) where
  isMine: Array.Vector Bool (n * m)

structure Minsweeper (n m: ℕ) where
  grid: Array.Vector (Option (Fin 9)) (n * m)

def toIndex (i: Fin n) (j: Fin m) : Fin (n * m) where
  val := i.val * m + j.val
  isLt := by
    refine Nat.mul_add_lt i j n ?_ ?_
    apply Fin.isLt
    apply Fin.isLt

instance : GetElem (MinsweeperData n m) (Fin n × Fin m) Bool (fun _ _ => True) where
  getElem d x _ := d.isMine[toIndex x.fst x.snd]

instance : GetElem (Minsweeper n m) (Fin n × Fin m) (Option (Fin 9)) (fun _ _ => True) where
  getElem d x _ := d.grid[toIndex x.fst x.snd]

namespace Nat

private def abs_diff (i j: ℕ) : ℕ := if i ≤ j then j - i else i - j

end Nat

namespace MinsweeperData

def minesAround (data: MinsweeperData n m) (i: Fin n) (j: Fin m) : Fin 9 :=
  match n with
  | n + 1 =>
  match m with
  | m + 1 =>

  have i₀ := i - 1
  have j₀ := j - 1
  have i₁ := i + 1
  have j₁ := j + 1

  Id.run do
    let mut count : Fin 9 := 0

    if Nat.abs_diff i₀ i = 1 ∧ Nat.abs_diff j₀ j = 1 then
      count ← count + if data[(i₀, j₀)] then 1 else 0
    else
      ()
    if Nat.abs_diff i₀ i = 1 then
      count ← count + if data[(i₀, j)] then 1 else 0
    else
      ()
    if Nat.abs_diff i₀ i = 1 ∧ Nat.abs_diff j₁ j = 1 then
      count ← count + if data[(i₀, j₁)] then 1 else 0
    else
      ()

    if Nat.abs_diff j₀ j = 1 then
      count ← count + if data[(i, j₀)] then 1 else 0
    else
      ()
    if Nat.abs_diff j₁ j = 1 then
      count ← count + if data[(i, j₁)] then 1 else 0
    else
      ()

    if Nat.abs_diff i₁ i = 1 ∧ Nat.abs_diff j₀ j = 1 then
      count ← count + if data[(i₁, j₀)] then 1 else 0
    else
      ()
    if Nat.abs_diff i₁ i = 1 then
      count ← count + if data[(i₁, j)] then 1 else 0
    else
      ()
    if Nat.abs_diff i₁ i = 1 ∧ Nat.abs_diff j₁ j = 1 then
      count ← count + if data[(i₁, j₁)] then 1 else 0
    else
      ()

    return count

def mines (data: MinsweeperData n m) :=
  data.isMine.toArray.foldl (· + if · then 1 else 0) 0

end MinsweeperData

namespace Minsweeper

def isValid (game: Minsweeper n m) (data: MinsweeperData n m) : Prop :=
  -- every tile in the game is either hidden or equal to the number of mines around the game data
   ∀(i: Fin n) (j: Fin m), game[(i, j)].all (fun x => x = data.minesAround i j)

instance (game: Minsweeper n m) (data: MinsweeperData n m) : Decidable (game.isValid data) :=
  inferInstanceAs (Decidable (∀_, _))

def reveal (game: Minsweeper n m) (data: MinsweeperData n m) (i: Fin n) (j: Fin m) : Minsweeper n m where
  grid := game.grid.set (toIndex i j) (data.minesAround i j)

-- a tile is doesn't have a mine in every possible board which is valid for this game
-- and has the given number of mines on the board
def isGuaranteedSafe (game: Minsweeper n m) (i: Fin n) (j: Fin m) (num_mines: ℕ) : Prop :=
  ∀data: MinsweeperData n m, data.mines = num_mines -> game.isValid data -> !data[(i, j)]

-- a board is solvable if it requires no guesses to find every mine
inductive IsSolvable (data: MinsweeperData n m) : Minsweeper n m -> Prop where
| solved (game: Minsweeper n m) :
  (∀(i: Fin n) (j: Fin m), game[(i, j)].isNone -> data[(i, j)]) ->
  IsSolvable data game
| reveal (game: Minsweeper n m) (i: Fin n) (j: Fin m) :
  game.isGuaranteedSafe i j data.mines ->
  IsSolvable data (game.reveal data i j) ->
  IsSolvable data game

end Minsweeper
