import Math.Type.Notation
import Math.Data.Fintype.Basic
import Math.Data.Fintype.Impls.Finset
import Math.Data.Finset.Basic

structure MinesweeperBoard (ι: Type*) where
  neighbors: ι -> Finset ι
  mines: Finset ι
  is_mine: ι -> Bool := by intro i; exact i ∈ mines
  neighbors_symm: ∀x y: ι, y ∈ neighbors x ↔ x ∈ neighbors y
  is_mine_spec: ∀i, is_mine i ↔ i ∈ mines

structure Minesweeper (ι: Type*) where
  -- .none if the cell hasn't been clicked on yet
  -- .some if the cell has been clicked on, and how many mines are around it
  count_mines: ι -> Option ℕ

def MinesweeperBoard.count_mines_around (i: ι) (board: MinesweeperBoard ι) : ℕ :=
  (board.neighbors i).val.fold (fun x => (· + if board.is_mine x then 1 else 0)) 0 (by
    intro x y h; dsimp; ac_rfl)

namespace Minesweeper

def IsCompatible (board: MinesweeperBoard ι) (ms: Minesweeper ι) : Prop :=
  ∀i: ι, (ms.count_mines i).all (fun n => n = board.count_mines_around i)

instance [Fintype ι] (board: MinesweeperBoard ι) (ms: Minesweeper ι) : Decidable (ms.IsCompatible board) :=
  inferInstanceAs (Decidable (∀_, _))

def empty (ι: Type*) : Minesweeper ι where
  count_mines _ := .none

def reveal [DecidableEq ι] (game: Minesweeper ι) (data: MinesweeperBoard ι) (i: ι) : Minesweeper ι where
  count_mines x :=
    if x = i then
      data.count_mines_around x
    else
      game.count_mines x

-- a tile is doesn't have a mine in every possible board which is compatible for this game
-- and has the given number of mines on the board
def IsGuaranteedSafe (game: Minesweeper ι) (i: ι) (num_mines: ℕ) : Prop :=
  ∀data: MinesweeperBoard ι, data.mines.card = num_mines -> game.IsCompatible data -> ¬data.is_mine i

def IsSolved (board: MinesweeperBoard ι) (game: Minesweeper ι) :=
  -- in a solved board, the only tiles which aren't revealed are the ones which are mines
  ∀(i: ι), (game.count_mines i).isNone -> board.is_mine i

-- a board is solvable if it requires no guesses to find every mine
inductive IsSolvable (board: MinesweeperBoard ι) : Minesweeper ι -> Prop where
| solved (game: Minesweeper ι) : game.IsSolved board -> IsSolvable board game
| reveal [DecidableEq ι] (game: Minesweeper ι) (i: ι) :
  game.IsGuaranteedSafe i board.mines.card ->
  -- if after revealing a tile the board is solvable, then the current board is also solvable
  IsSolvable board (game.reveal board i) ->
  IsSolvable board game

instance [DecidableEq ι] : WellFoundedRelation { ms: Minesweeper ι // ms.IsSolvable board ∧ ms.IsCompatible board } where
  rel a b := ∃i,
    a.val = b.val.reveal board i ∧
    b.val.IsGuaranteedSafe i board.mines.card ∧
    (b.val.count_mines i).isNone
  wf := by
    apply WellFounded.intro
    intro ⟨ms, h, compat⟩
    induction h with
    | solved ms solved =>
      apply Acc.intro
      intro ⟨ms', h', compat'⟩ h
      obtain ⟨i, rfl, safe, nomine⟩ := h
      dsimp at *
      have := safe board rfl compat
      have := solved i nomine
      contradiction
    | reveal ms i safe solvable ih =>
      apply Acc.intro
      intro ⟨ms', h', compat'⟩ h
      obtain ⟨j, rfl, safe, nomine⟩ := h
      dsimp at *
      apply ih
      sorry

end Minesweeper
