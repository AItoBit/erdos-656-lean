module

public import Mathlib.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace Palomar656

/-- Number of selected natural numbers in the prefix [0,N). -/
noncomputable def countIn (numbers : Set ℕ) (size : ℕ) : ℕ := by
  classical
  exact ((Finset.range size).filter (· ∈ numbers)).card

/-- Ordinary upper asymptotic density, computed using prefix intervals. -/
noncomputable def upperDensity (numbers : Set ℕ) : ℝ :=
  Filter.limsup (fun size : ℕ => (countIn numbers size : ℝ) / size) Filter.atTop

/-- One integer translate of every restricted pair sum lies in the original set. -/
def HasTranslatedRestrictedPairSums (numbers selected : Set ℕ) : Prop :=
  ∃ shift : ℤ, ∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
    ∃ result ∈ numbers, (result : ℤ) = (first : ℤ) + second + shift

/-- Every set of natural numbers of positive ordinary upper density contains an infinite subset
whose distinct pair sums all return to the original set after one integer translation.
This is Erdős Problem 656, an instance of Kra–Moreira–Richter–Robertson Theorem 1.2(i). -/
theorem erdos_656 {numbers : Set ℕ} (positive_density : 0 < upperDensity numbers) :
    ∃ selected : Set ℕ, selected.Infinite ∧ selected ⊆ numbers ∧
      HasTranslatedRestrictedPairSums numbers selected := by
  sorry

end Palomar656
