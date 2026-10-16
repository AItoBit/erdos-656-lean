module

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 656.
https://www.erdosproblems.com/forum/thread/656

Informal authors:
- Bryna Kra
- Joel Moreira
- Florian K. Richter
- Donald Robertson

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos656.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 656.
https://www.erdosproblems.com/656

Informal authors:
- Bryna Kra
- Joel Moreira
- Florian K. Richter
- Donald Robertson

Formal authors:
- OpenAI Codex

Primary source:
- B. Kra, J. Moreira, F. K. Richter, and D. Robertson,
  "A proof of Erdős's B+B+t conjecture", Commun. Amer. Math. Soc. 4 (2024),
  480--494.  arXiv:2206.12377.
-/

public import Mathlib.Combinatorics.Hindman
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Dynamics.Ergodic.Extreme
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.Dynamics.Ergodic.Action.OfMinimal
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

/- The diagonal spectral-measure construction below is adapted from the Apache-2.0
licensed Kitware AIQ development by Jon Crall, Claude Opus 5, and OpenAI Codex. -/
@[expose] public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

section OfReal

variable {X : Type*} [TopologicalSpace X]

/-- Complexification of a real continuous function, as an `ℝ`-linear map. -/
noncomputable def ofRealLM : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun g := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  map_add' g g' := by ext x; simp
  map_smul' r g := by ext x; simp

/-- The real-to-complex coercion of a continuous function, pointwise. -/
@[simp] theorem ofRealLM_apply (g : C(X, ℝ)) (x : X) :
    ofRealLM g x = (g x : ℂ) := (rfl)
/-- A real-valued symbol is star-invariant, which is why its calculus is self-adjoint. -/
@[simp] theorem star_ofRealLM (g : C(X, ℝ)) : star (ofRealLM g) = ofRealLM g := by
  ext x; simp

end OfReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Positivity

variable (ha : IsStarNormal a)

/-- A real continuous symbol has self-adjoint functional-calculus image. -/
theorem isSelfAdjoint_cfcHom_ofReal (g : C(spectrum ℂ a, ℝ)) :
    IsSelfAdjoint (cfcHom ha (ofRealLM g)) := by
  rw [IsSelfAdjoint, ← map_star, star_ofRealLM]

/-- The diagonal value of a real symbol is real. -/
theorem inner_cfcHom_ofReal_conj (g : C(spectrum ℂ a, ℝ)) (ξ : H) :
    (starRingEnd ℂ) ⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ = ⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ := by
  rw [inner_conj_symm]
  conv_lhs => rw [← (isSelfAdjoint_cfcHom_ofReal ha g).star_eq]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- For a real symbol the diagonal matrix element is real, so taking `re` and coercing back is the
identity.  This is what lets the diagonal functional be defined over `ℝ`. -/
theorem inner_cfcHom_ofReal_re (g : C(spectrum ℂ a, ℝ)) (ξ : H) :
    (((⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ).re : ℝ) : ℂ) =
      ⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ :=
  Complex.conj_eq_iff_re.mp (inner_cfcHom_ofReal_conj ha g ξ)

/-- Positivity: a nonnegative real symbol has nonnegative diagonal values. -/
theorem inner_cfcHom_ofReal_nonneg {g : C(spectrum ℂ a, ℝ)} (hg : ∀ x, 0 ≤ g x) (ξ : H) :
    0 ≤ (⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ).re := by
  set k : C(spectrum ℂ a, ℝ) :=
    ⟨fun x => Real.sqrt (g x), Real.continuous_sqrt.comp g.continuous⟩ with hk
  have hsq : ofRealLM k * ofRealLM k = ofRealLM g := by
    ext x
    simp only [ContinuousMap.mul_apply, ofRealLM_apply, hk, ContinuousMap.coe_mk,
      ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (hg x)]
  have hstar : cfcHom ha (ofRealLM k) =
      ContinuousLinearMap.adjoint (cfcHom ha (ofRealLM k)) := by
    conv_lhs => rw [← star_ofRealLM k, map_star]
    rfl
  have h1 : cfcHom ha (ofRealLM g) ξ =
      ContinuousLinearMap.adjoint (cfcHom ha (ofRealLM k)) (cfcHom ha (ofRealLM k) ξ) := by
    rw [← hsq, map_mul, ← hstar]; rfl
  have hnorm : ⟪cfcHom ha (ofRealLM k) ξ, cfcHom ha (ofRealLM k) ξ⟫_ℂ =
      ((‖cfcHom ha (ofRealLM k) ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h1, ContinuousLinearMap.adjoint_inner_right, hnorm, Complex.ofReal_re]
  positivity

end Positivity

section Functional

variable (ha : IsStarNormal a)

/-- The positive linear functional `f ↦ ⟪ξ, cfcHom f ξ⟫` on real continuous
functions over the spectrum. -/
noncomputable def diagFunctional (ξ : H) :
    C_c(spectrum ℂ a, ℝ) →ₚ[ℝ] ℝ where
  toFun g := (⟪ξ, cfcHom ha (ofRealLM g.toContinuousMap) ξ⟫_ℂ).re
  map_add' g g' := by
    have h : (g + g').toContinuousMap = g.toContinuousMap + g'.toContinuousMap := (rfl)
    rw [h, map_add, map_add, _root_.add_apply, inner_add_right, Complex.add_re]
  map_smul' r g := by
    have h : (r • g).toContinuousMap = r • g.toContinuousMap := (rfl)
    have hc : ofRealLM (r • g.toContinuousMap) =
        (r : ℂ) • ofRealLM g.toContinuousMap := by
      ext x; simp [Complex.real_smul]
    rw [h, hc, map_smul, _root_.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
    rfl
  monotone' g g' hgg' := by
    have hle : ∀ x, g x ≤ g' x := fun x => hgg' x
    have hdnn : ∀ x, 0 ≤ (g'.toContinuousMap - g.toContinuousMap) x :=
      fun x => sub_nonneg.mpr (hle x)
    have hpos := inner_cfcHom_ofReal_nonneg ha hdnn ξ
    rw [map_sub, map_sub, _root_.sub_apply, inner_sub_right, Complex.sub_re] at hpos
    linarith

/-- The diagonal functional, unfolded to the integral it is. -/
@[simp] theorem diagFunctional_apply (ξ : H) (g : C_c(spectrum ℂ a, ℝ)) :
    diagFunctional ha ξ g = (⟪ξ, cfcHom ha (ofRealLM g.toContinuousMap) ξ⟫_ℂ).re := (rfl)
/-- The **diagonal spectral measure** of a normal operator at a vector. -/
noncomputable def diagMeasure (ξ : H) : Measure (spectrum ℂ a) :=
  RealRMK.rieszMeasure (diagFunctional ha ξ)

/-- Equal diagonal functionals give equal diagonal measures, since the measure is produced from the
functional by Riesz representation. -/
theorem diagMeasure_congr {ξ η : H} (h : diagFunctional ha ξ = diagFunctional ha η) :
    diagMeasure ha ξ = diagMeasure ha η := by
  rw [diagMeasure, diagMeasure, h]

/-- Diagonal measures are finite, inherited from the Riesz measure of a bounded functional. -/
instance instIsFiniteMeasure_diagMeasure (ξ : H) :
    IsFiniteMeasure (diagMeasure ha ξ) := by
  unfold diagMeasure; infer_instance

/-- Diagonal measures are regular, which is what allows continuous symbols to be approximated by
simple ones in the Borel calculus. -/
instance instRegular_diagMeasure (ξ : H) : (diagMeasure ha ξ).Regular := by
  unfold diagMeasure; infer_instance

/-- Continuous functions are integrable against a diagonal measure: the
spectrum is compact and the measure is finite. -/
theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ξ : H) (f : C(spectrum ℂ a, E)) : Integrable f (diagMeasure ha ξ) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Riesz–Markov–Kakutani, specialised: real symbols integrate to diagonal
values of the continuous functional calculus. -/
theorem integral_diagMeasure_ofReal (ξ : H) (g : C(spectrum ℂ a, ℝ)) :
    ∫ x, g x ∂(diagMeasure ha ξ) = (⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ).re :=
  RealRMK.integral_rieszMeasure (diagFunctional ha ξ)
    (⟨g, HasCompactSupport.of_compactSpace g⟩ : C_c(spectrum ℂ a, ℝ))

/-- **The defining property of the diagonal measure.**  Integrating a
continuous symbol against `diagMeasure ha ξ` reproduces the diagonal matrix
element of its functional-calculus image. -/
theorem integral_diagMeasure (ξ : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ x, f x ∂(diagMeasure ha ξ) = ⟪ξ, cfcHom ha f ξ⟫_ℂ := by
  set u : C(spectrum ℂ a, ℝ) :=
    ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩ with hu
  set v : C(spectrum ℂ a, ℝ) :=
    ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩ with hv
  have hf : f = ofRealLM u + Complex.I • ofRealLM v := by
    ext x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im (f x)).symm
  have hiu : Integrable (fun x => ((u x : ℝ) : ℂ)) (diagMeasure ha ξ) :=
    integrable_of_continuous ha ξ (ofRealLM u)
  have hiv : Integrable (fun x => ((v x : ℝ) : ℂ)) (diagMeasure ha ξ) :=
    integrable_of_continuous ha ξ (ofRealLM v)
  have hlhs : ∫ x, f x ∂(diagMeasure ha ξ) =
      ((∫ x, u x ∂(diagMeasure ha ξ) : ℝ) : ℂ) +
        Complex.I * ((∫ x, v x ∂(diagMeasure ha ξ) : ℝ) : ℂ) := by
    conv_lhs => rw [hf]
    rw [show (fun x => (ofRealLM u + Complex.I • ofRealLM v) x) =
        (fun x => ((u x : ℝ) : ℂ) + Complex.I * ((v x : ℝ) : ℂ)) from rfl,
      integral_add hiu (hiv.const_mul Complex.I), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal]
  rw [hlhs, integral_diagMeasure_ofReal, integral_diagMeasure_ofReal,
    inner_cfcHom_ofReal_re, inner_cfcHom_ofReal_re]
  conv_rhs => rw [hf]
  rw [map_add, map_smul, _root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_smul_right]

/-- The total mass of a diagonal measure is `‖ξ‖ ^ 2`. -/
@[simp] theorem diagMeasure_univ_toReal (ξ : H) :
    ((diagMeasure ha ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := integral_diagMeasure ha ξ 1
  simp only [ContinuousMap.one_apply] at h
  rw [integral_const, Complex.real_smul, mul_one, MeasureTheory.measureReal_def, map_one] at h
  have h2 : ⟪ξ, (1 : H →L[ℂ] H) ξ⟫_ℂ = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [one_apply_eq_self, inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h2] at h
  exact_mod_cast h

end Functional

end BorelCalculus
end TauCeti


open Filter Function Set Topology MeasureTheory
open scoped ENNReal Topology ComplexConjugate InnerProductSpace

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace Erdos656
namespace Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def scaledUnitary (u : unitary (H →L[ℂ] H)) (lambda : ℂ) :
    H →L[ℂ] H := lambda⁻¹ • (u : H →L[ℂ] H)

theorem norm_scaledUnitary_le_one (u : unitary (H →L[ℂ] H))
    {lambda : ℂ} (hlambda : ‖lambda‖ = 1) :
    ‖scaledUnitary u lambda‖ ≤ 1 := by
  rw [scaledUnitary, norm_smul, norm_inv, hlambda, inv_one, one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using le_of_eq (Unitary.norm_map u x)

theorem tendsto_scaledUnitary_average_zero
    (u : unitary (H →L[ℂ] H)) {lambda : ℂ} (hlambda : ‖lambda‖ = 1)
    (xi : H) (hxi : ∀ v : H, (u : H →L[ℂ] H) v = lambda • v → inner ℂ v xi = 0) :
    Tendsto (fun n ↦ birkhoffAverage ℂ (scaledUnitary u lambda) id n xi)
      atTop (nhds 0) := by
  let S : Submodule ℂ H :=
    (scaledUnitary u lambda).eqLocus (1 : H →L[ℂ] H)
  have horth : xi ∈ S.orthogonal := by
    intro v hv
    apply hxi v
    have hv' : lambda⁻¹ • (u : H →L[ℂ] H) v = v := hv
    have hlambda0 : lambda ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlambda
      norm_num at hlambda
    calc
      (u : H →L[ℂ] H) v = (1 : ℂ) • (u : H →L[ℂ] H) v := by simp
      _ = (lambda * lambda⁻¹) • (u : H →L[ℂ] H) v := by
        rw [mul_inv_cancel₀ hlambda0]
      _ = lambda • (lambda⁻¹ • (u : H →L[ℂ] H) v) := by rw [mul_smul]
      _ = lambda • v := by rw [hv']
  have hproj : S.orthogonalProjectionOnto xi = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr horth
  have h := (scaledUnitary u lambda).tendsto_birkhoffAverage_orthogonalProjection
    (norm_scaledUnitary_le_one u hlambda) xi
  have hproj' : (S.orthogonalProjectionOnto xi : H) = 0 := by
    exact congrArg Subtype.val hproj
  change Tendsto (fun n ↦ birkhoffAverage ℂ (scaledUnitary u lambda) id n xi)
      atTop (nhds (S.orthogonalProjectionOnto xi : H)) at h
  rwa [hproj'] at h

noncomputable def spectralCesaro (u : unitary (H →L[ℂ] H)) (lambda : ℂ)
    (n : ℕ) : C(spectrum ℂ (u : H →L[ℂ] H), ℂ) :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n,
    (lambda⁻¹ • ContinuousMap.restrict (spectrum ℂ (u : H →L[ℂ] H))
      (ContinuousMap.id ℂ)) ^ k

theorem spectralCesaro_apply (u : unitary (H →L[ℂ] H)) (lambda : ℂ)
    (n : ℕ) (z : spectrum ℂ (u : H →L[ℂ] H)) :
    spectralCesaro u lambda n z =
      (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, (lambda⁻¹ * (z : ℂ)) ^ k := by
  simp [spectralCesaro]

theorem pow_scaledUnitary_apply (u : unitary (H →L[ℂ] H)) (lambda : ℂ)
    (k : ℕ) (xi : H) :
    ((scaledUnitary u lambda) ^ k) xi =
      (scaledUnitary u lambda : H → H)^[k] xi := by
  induction k generalizing xi with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      rfl

theorem cfcHom_spectralCesaro_apply (u : unitary (H →L[ℂ] H)) (lambda : ℂ)
    (n : ℕ) (xi : H) :
    cfcHom (Unitary.coe_isStarNormal u) (spectralCesaro u lambda n) xi =
      birkhoffAverage ℂ (scaledUnitary u lambda) id n xi := by
  rw [spectralCesaro, map_smul, map_sum]
  simp only [map_pow, map_smul, cfcHom_id, _root_.smul_apply, birkhoffAverage]
  congr 1
  simp only [birkhoffSum, scaledUnitary]
  rw [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact pow_scaledUnitary_apply u lambda k xi

theorem integral_norm_sq_diagMeasure (u : unitary (H →L[ℂ] H))
    (xi : H) (f : C(spectrum ℂ (u : H →L[ℂ] H), ℂ)) :
    ∫ z, ‖f z‖ ^ 2 ∂(TauCeti.BorelCalculus.diagMeasure
      (Unitary.coe_isStarNormal u) xi) =
      ‖cfcHom (Unitary.coe_isStarNormal u) f xi‖ ^ 2 := by
  let g : C(spectrum ℂ (u : H →L[ℂ] H), ℂ) := star f * f
  have hg : ∀ z, g z = ((‖f z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    simp only [g, ContinuousMap.mul_apply, ContinuousMap.star_apply]
    change (starRingEnd ℂ) (f z) * f z = ((‖f z‖ ^ 2 : ℝ) : ℂ)
    calc
      (starRingEnd ℂ) (f z) * f z = ((‖f z‖ : ℝ) : ℂ) ^ 2 := RCLike.conj_mul (f z)
      _ = ((‖f z‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  have h := TauCeti.BorelCalculus.integral_diagMeasure (Unitary.coe_isStarNormal u) xi g
  have hleft : ∫ z, g z ∂(TauCeti.BorelCalculus.diagMeasure
      (Unitary.coe_isStarNormal u) xi) =
      ((∫ z, ‖f z‖ ^ 2 ∂(TauCeti.BorelCalculus.diagMeasure
        (Unitary.coe_isStarNormal u) xi) : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hg), integral_complex_ofReal]
  have hright : ⟪xi, cfcHom (Unitary.coe_isStarNormal u) g xi⟫_ℂ =
      ((‖cfcHom (Unitary.coe_isStarNormal u) f xi‖ ^ 2 : ℝ) : ℂ) := by
    dsimp only [g]
    rw [map_mul, map_star]
    change ⟪xi, ContinuousLinearMap.adjoint (cfcHom (Unitary.coe_isStarNormal u) f)
      (cfcHom (Unitary.coe_isStarNormal u) f xi)⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hleft, hright] at h
  exact_mod_cast h

theorem spectrum_unitary_norm (u : unitary (H →L[ℂ] H))
    (z : spectrum ℂ (u : H →L[ℂ] H)) : ‖(z : ℂ)‖ = 1 := by
  have hz := spectrum.subset_circle_of_unitary u.property z.property
  simpa only [Metric.mem_sphere, dist_zero_right] using hz

theorem spectralCesaro_self_succ (u : unitary (H →L[ℂ] H))
    (z : spectrum ℂ (u : H →L[ℂ] H)) (n : ℕ) :
    spectralCesaro u (z : ℂ) (n + 1) z = 1 := by
  rw [spectralCesaro_apply]
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hz
    have := spectrum_unitary_norm u z
    rw [hz, norm_zero] at this
    norm_num at this
  rw [inv_mul_cancel₀ hz0]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [mul_one]
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [inv_mul_cancel₀ hn]

theorem diagMeasure_singleton_eq_zero_of_orthogonal_eigenvectors
    (u : unitary (H →L[ℂ] H)) (xi : H)
    (hxi : ∀ (lambda : ℂ) (v : H), (u : H →L[ℂ] H) v = lambda • v →
      inner ℂ v xi = 0)
    (z : spectrum ℂ (u : H →L[ℂ] H)) :
    TauCeti.BorelCalculus.diagMeasure (Unitary.coe_isStarNormal u) xi {z} = 0 := by
  let mu : Measure (spectrum ℂ (u : H →L[ℂ] H)) :=
    TauCeti.BorelCalculus.diagMeasure (Unitary.coe_isStarNormal u) xi
  have havg := tendsto_scaledUnitary_average_zero u (spectrum_unitary_norm u z) xi
    (fun v hv ↦ hxi (z : ℂ) v hv)
  have havg' := havg.comp (tendsto_add_atTop_nat 1)
  have hnorm : Tendsto
      (fun n ↦ ‖birkhoffAverage ℂ (scaledUnitary u (z : ℂ)) id (n + 1) xi‖ ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_norm.comp havg').pow 2
  have hint : Tendsto
      (fun n ↦ ∫ w, ‖spectralCesaro u (z : ℂ) (n + 1) w‖ ^ 2 ∂mu)
      atTop (nhds 0) := by
    apply hnorm.congr'
    filter_upwards [] with n
    rw [integral_norm_sq_diagMeasure, cfcHom_spectralCesaro_apply]
  have hle : ∀ n : ℕ, mu.real {z} ≤
      ∫ w, ‖spectralCesaro u (z : ℂ) (n + 1) w‖ ^ 2 ∂mu := by
    intro n
    have hc : Continuous
        (fun w ↦ ‖spectralCesaro u (z : ℂ) (n + 1) w‖ ^ 2) :=
      (spectralCesaro u (z : ℂ) (n + 1)).continuous.norm.pow 2
    have hi : Integrable
        (fun w ↦ ‖spectralCesaro u (z : ℂ) (n + 1) w‖ ^ 2) mu :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmono := setIntegral_le_integral (s := {z}) hi
      (Filter.Eventually.of_forall (fun w ↦ sq_nonneg _))
    rw [integral_singleton, spectralCesaro_self_succ, norm_one, one_pow, smul_eq_mul,
      mul_one] at hmono
    exact hmono
  have hreal_nonpos : mu.real {z} ≤ 0 := ge_of_tendsto hint
    (Filter.Eventually.of_forall hle)
  have hreal : mu.real {z} = 0 := le_antisymm hreal_nonpos (by positivity)
  have htor : mu {z} = 0 ∨ mu {z} = ∞ := by
    apply (ENNReal.toReal_eq_zero_iff (mu {z})).mp
    simpa only [measureReal_def] using hreal
  rcases htor with hzero | hinf
  · exact hzero
  · exact (measure_ne_top mu {z} hinf).elim

noncomputable def geometricCesaro (n : ℕ) (q : ℂ) : ℂ :=
  (((n + 1 : ℕ) : ℂ))⁻¹ * ∑ k ∈ Finset.range (n + 1), q ^ k

theorem norm_geometricCesaro_le_one {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) :
    ‖geometricCesaro n q‖ ≤ 1 := by
  rw [geometricCesaro, norm_mul, norm_inv, norm_natCast]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    ((n : ℝ) + 1)⁻¹ * ‖∑ k ∈ Finset.range (n + 1), q ^ k‖
        ≤ ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), ‖q ^ k‖ := by
          gcongr
          exact norm_sum_le _ _
    _ = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := by simp [norm_pow, hq]
    _ = 1 := by
      rw [inv_mul_cancel₀]
      positivity

theorem tendsto_geometricCesaro_zero {q : ℂ} (hqnorm : ‖q‖ = 1) (hq : q ≠ 1) :
    Tendsto (fun n ↦ geometricCesaro n q) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ norm (((n + 1 : ℕ) : ℂ)⁻¹))
      atTop (nhds 0) := by
    have hcomplex : Tendsto (fun n : ℕ ↦ (((n : ℂ) + 1))⁻¹)
        atTop (nhds 0) := by
      simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
    simpa only [Nat.cast_add, Nat.cast_one, norm_zero] using hcomplex.norm
  have hbound : Tendsto
      (fun n : ℕ ↦ norm (((n + 1 : ℕ) : ℂ)⁻¹) * (2 / ‖q - 1‖))
      atTop (nhds 0) := by
    simpa using hinv.mul_const (2 / ‖q - 1‖)
  apply squeeze_zero_norm (a := fun n : ℕ ↦
      norm (((n + 1 : ℕ) : ℂ)⁻¹) * (2 / ‖q - 1‖))
  · intro n
    rw [geometricCesaro, geom_sum_eq hq, norm_mul, norm_div]
    gcongr
    exact (norm_sub_le _ _).trans_eq (by
      rw [norm_pow, hqnorm, one_pow, norm_one]
      norm_num)
  · exact hbound

noncomputable def wienerKernel (u : unitary (H →L[ℂ] H)) (n : ℕ)
    (p : spectrum ℂ (u : H →L[ℂ] H) × spectrum ℂ (u : H →L[ℂ] H)) : ℂ :=
  geometricCesaro n ((starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ))

theorem measure_prod_diagonal_eq_zero
    (u : unitary (H →L[ℂ] H))
    (mu : Measure (spectrum ℂ (u : H →L[ℂ] H))) [IsFiniteMeasure mu]
    (hsingleton : ∀ z, mu {z} = 0) :
    mu.prod mu (Set.diagonal (spectrum ℂ (u : H →L[ℂ] H))) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  calc
    ∫⁻ z, mu (Prod.mk z ⁻¹' Set.diagonal
        (spectrum ℂ (u : H →L[ℂ] H))) ∂mu = ∫⁻ _z, 0 ∂mu := by
      apply lintegral_congr
      intro z
      have hset : Prod.mk z ⁻¹' Set.diagonal
          (spectrum ℂ (u : H →L[ℂ] H)) = {z} := by
        ext w
        simp [Set.mem_diagonal_iff, eq_comm]
      rw [hset, hsingleton]
    _ = 0 := lintegral_zero

theorem wienerKernel_tendsto_integral_zero
    (u : unitary (H →L[ℂ] H))
    (mu : Measure (spectrum ℂ (u : H →L[ℂ] H))) [IsFiniteMeasure mu]
    (hsingleton : ∀ z, mu {z} = 0) :
    Tendsto (fun n ↦ ∫ p, wienerKernel u n p ∂(mu.prod mu)) atTop (nhds 0) := by
  have hdiag := measure_prod_diagonal_eq_zero u mu hsingleton
  have hae_ne : ∀ᵐ p ∂(mu.prod mu), p.1 ≠ p.2 := by
    apply ae_iff.mpr
    have hset : {p : spectrum ℂ (u : H →L[ℂ] H) ×
        spectrum ℂ (u : H →L[ℂ] H) | ¬p.1 ≠ p.2} =
        Set.diagonal (spectrum ℂ (u : H →L[ℂ] H)) := by
      ext p
      simp [Set.mem_diagonal_iff]
    rw [hset]
    exact hdiag
  have hlim : ∀ᵐ p ∂(mu.prod mu),
      Tendsto (fun n ↦ wienerKernel u n p) atTop (nhds 0) := by
    filter_upwards [hae_ne] with p hp
    have hqnorm : ‖(starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ)‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, spectrum_unitary_norm u p.1,
        spectrum_unitary_norm u p.2, one_mul]
    have hq : (starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ) ≠ 1 := by
      intro heq
      apply hp
      apply Subtype.ext
      calc
        (p.1 : ℂ) = (p.1 : ℂ) * 1 := by simp
        _ = (p.1 : ℂ) * ((starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ)) := by rw [heq]
        _ = ((p.1 : ℂ) * (starRingEnd ℂ) (p.1 : ℂ)) * (p.2 : ℂ) := by
          rw [mul_assoc]
        _ = (p.2 : ℂ) := by
          rw [RCLike.mul_conj, spectrum_unitary_norm u p.1]
          norm_num
    exact tendsto_geometricCesaro_zero hqnorm hq
  have hmeas : ∀ n, AEStronglyMeasurable (wienerKernel u n) (mu.prod mu) := by
    intro n
    apply Continuous.aestronglyMeasurable
    unfold wienerKernel geometricCesaro
    fun_prop
  have hbound : ∀ n, ∀ᵐ p ∂(mu.prod mu), ‖wienerKernel u n p‖ ≤ 1 := by
    intro n
    filter_upwards [] with p
    apply norm_geometricCesaro_le_one
    rw [norm_mul, RCLike.norm_conj, spectrum_unitary_norm u p.1,
      spectrum_unitary_norm u p.2, one_mul]
  have hone : Integrable (fun _ : spectrum ℂ (u : H →L[ℂ] H) ×
      spectrum ℂ (u : H →L[ℂ] H) ↦ (1 : ℝ)) (mu.prod mu) :=
    integrable_const 1
  have h := tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    hmeas hone hbound hlim
  simpa using h

theorem integral_wienerKernel_eq
    (u : unitary (H →L[ℂ] H))
    (mu : Measure (spectrum ℂ (u : H →L[ℂ] H))) [IsFiniteMeasure mu]
    (n : ℕ) :
    ∫ p, wienerKernel u n p ∂(mu.prod mu) =
      (((n + 1 : ℕ) : ℂ))⁻¹ * ∑ k ∈ Finset.range (n + 1),
        ((‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2 : ℝ) : ℂ) := by
  unfold wienerKernel geometricCesaro
  rw [integral_const_mul]
  have hint : ∀ k ∈ Finset.range (n + 1), Integrable
      (fun p : spectrum ℂ (u : H →L[ℂ] H) ×
        spectrum ℂ (u : H →L[ℂ] H) ↦
          ((starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ)) ^ k) (mu.prod mu) := by
    intro k hk
    have hc : Continuous
        (fun p : spectrum ℂ (u : H →L[ℂ] H) ×
          spectrum ℂ (u : H →L[ℂ] H) ↦
            ((starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ)) ^ k) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ hint]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hfun : (fun p : spectrum ℂ (u : H →L[ℂ] H) ×
      spectrum ℂ (u : H →L[ℂ] H) ↦
        ((starRingEnd ℂ) (p.1 : ℂ) * (p.2 : ℂ)) ^ k) =
      (fun p ↦ (starRingEnd ℂ) ((p.1 : ℂ) ^ k) * ((p.2 : ℂ) ^ k)) := by
    funext p
    rw [mul_pow, map_pow]
  rw [hfun]
  calc
    ∫ p : spectrum ℂ (u : H →L[ℂ] H) × spectrum ℂ (u : H →L[ℂ] H),
        (starRingEnd ℂ) ((p.1 : ℂ) ^ k) * ((p.2 : ℂ) ^ k) ∂(mu.prod mu) =
        (∫ z, (starRingEnd ℂ) ((z : ℂ) ^ k) ∂mu) *
          ∫ z, ((z : ℂ) ^ k) ∂mu :=
      MeasureTheory.integral_prod_mul
        (fun z : spectrum ℂ (u : H →L[ℂ] H) ↦
          (starRingEnd ℂ) ((z : ℂ) ^ k))
        (fun z : spectrum ℂ (u : H →L[ℂ] H) ↦ ((z : ℂ) ^ k))
    _ = ((‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2 : ℝ) : ℂ) := by
      rw [integral_conj, RCLike.conj_mul]
      norm_cast

theorem wiener_mean_square_tendsto_zero
    (u : unitary (H →L[ℂ] H))
    (mu : Measure (spectrum ℂ (u : H →L[ℂ] H))) [IsFiniteMeasure mu]
    (hsingleton : ∀ z, mu {z} = 0) :
    Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), ‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2)
      atTop (nhds 0) := by
  have h := wienerKernel_tendsto_integral_zero u mu hsingleton
  have hc : Tendsto (fun n ↦ (((n + 1 : ℕ) : ℂ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1),
        ((‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2 : ℝ) : ℂ)) atTop (nhds 0) := by
    simpa only [integral_wienerKernel_eq] using h
  have hre := (Complex.continuous_re.tendsto 0).comp hc
  have hpoint : ∀ n : ℕ,
      (((((n + 1 : ℕ) : ℂ))⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          ((‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2 : ℝ) : ℂ))).re =
        (((n + 1 : ℕ) : ℝ))⁻¹ *
          ∑ k ∈ Finset.range (n + 1), ‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2 := by
    intro n
    have hcast : (((n + 1 : ℕ) : ℂ))⁻¹ =
        (((((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    have hsum : (∑ k ∈ Finset.range (n + 1),
        ((‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2 : ℝ) : ℂ)) =
        (((∑ k ∈ Finset.range (n + 1),
          ‖∫ z, ((z : ℂ) ^ k) ∂mu‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, hsum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre' := hre.congr' (Filter.Eventually.of_forall (fun n ↦ hpoint n))
  simpa only [Function.comp_apply, Complex.zero_re] using hre'

theorem integral_monomial_diagMeasure (u : unitary (H →L[ℂ] H))
    (xi : H) (k : ℕ) :
    ∫ z, ((z : ℂ) ^ k) ∂(TauCeti.BorelCalculus.diagMeasure
      (Unitary.coe_isStarNormal u) xi) = ⟪xi, ((u : H →L[ℂ] H) ^ k) xi⟫_ℂ := by
  let idSpectrum : C(spectrum ℂ (u : H →L[ℂ] H), ℂ) :=
    ContinuousMap.restrict (spectrum ℂ (u : H →L[ℂ] H)) (ContinuousMap.id ℂ)
  have h := TauCeti.BorelCalculus.integral_diagMeasure (Unitary.coe_isStarNormal u) xi
    (idSpectrum ^ k)
  simpa only [idSpectrum, ContinuousMap.pow_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply, map_pow, cfcHom_id] using h

theorem unitary_correlation_mean_square_tendsto_zero
    (u : unitary (H →L[ℂ] H)) (xi : H)
    (hxi : ∀ (lambda : ℂ) (v : H), (u : H →L[ℂ] H) v = lambda • v →
      inner ℂ v xi = 0) :
    Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), ‖⟪xi, ((u : H →L[ℂ] H) ^ k) xi⟫_ℂ‖ ^ 2)
      atTop (nhds 0) := by
  let mu : Measure (spectrum ℂ (u : H →L[ℂ] H)) :=
    TauCeti.BorelCalculus.diagMeasure (Unitary.coe_isStarNormal u) xi
  have hsingle : ∀ z, mu {z} = 0 :=
    diagMeasure_singleton_eq_zero_of_orthogonal_eigenvectors u xi hxi
  have h := wiener_mean_square_tendsto_zero u mu hsingle
  simpa only [mu, integral_monomial_diagMeasure] using h

omit [CompleteSpace H] in
theorem pow_continuousLinearMap_apply (A : H →L[ℂ] H) (k : ℕ) (v : H) :
    (A ^ k) v = (A : H → H)^[k] v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      rfl

theorem tendsto_birkhoffAverage_zero_of_correlationMean_zero
    (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (v : H)
    (hcorr : Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), ‖⟪v, (A ^ k) v⟫_ℂ‖) atTop (nhds 0)) :
    Tendsto (fun n ↦ birkhoffAverage ℂ A id (n + 1) v) atTop (nhds 0) := by
  let S : Submodule ℂ H := A.eqLocus (1 : H →L[ℂ] H)
  let p : H := (S.orthogonalProjectionOnto v : H)
  have havg : Tendsto (fun n ↦ birkhoffAverage ℂ A id (n + 1) v)
      atTop (nhds p) := by
    have h := A.tendsto_birkhoffAverage_orthogonalProjection hA v
    change Tendsto (fun n ↦ birkhoffAverage ℂ A id n v) atTop (nhds p) at h
    exact h.comp (tendsto_add_atTop_nat 1)
  have hinnerlim : Tendsto
      (fun n ↦ ⟪v, birkhoffAverage ℂ A id (n + 1) v⟫_ℂ)
      atTop (nhds ⟪v, p⟫_ℂ) :=
    (tendsto_const_nhds.inner havg)
  have hinnerzero : Tendsto
      (fun n ↦ ⟪v, birkhoffAverage ℂ A id (n + 1) v⟫_ℂ)
      atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), ‖⟪v, (A ^ k) v⟫_ℂ‖)
    · intro n
      rw [birkhoffAverage, inner_smul_right, norm_mul]
      have hn : 0 ≤ (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
      rw [norm_inv, norm_natCast]
      gcongr
      rw [birkhoffSum, inner_sum]
      calc
        ‖∑ k ∈ Finset.range (n + 1), ⟪v, id ((A : H → H)^[k] v)⟫_ℂ‖ ≤
            ∑ k ∈ Finset.range (n + 1), ‖⟪v, id ((A : H → H)^[k] v)⟫_ℂ‖ :=
          norm_sum_le _ _
        _ = ∑ k ∈ Finset.range (n + 1), ‖⟪v, (A ^ k) v⟫_ℂ‖ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [pow_continuousLinearMap_apply]
          rfl
    · exact hcorr
  have hip : ⟪v, p⟫_ℂ = 0 := tendsto_nhds_unique hinnerlim hinnerzero
  have hpzero : p = 0 := by
    have horth := S.sub_starProjection_mem_orthogonal v
    have hpo : ⟪p, v - p⟫_ℂ = 0 := by
      exact horth (S.orthogonalProjectionOnto v) (S.orthogonalProjectionOnto v).property
    have hpv : ⟪p, v⟫_ℂ = ⟪p, p⟫_ℂ := by
      rw [inner_sub_right, sub_eq_zero] at hpo
      exact hpo
    have hvp : ⟪p, v⟫_ℂ = 0 := by
      have h := congrArg (starRingEnd ℂ) hip
      simpa only [inner_conj_symm, map_zero] using h
    have hself : ⟪p, p⟫_ℂ = 0 := hpv.symm.trans hvp
    exact inner_self_eq_zero.mp hself
  rwa [hpzero] at havg

theorem tendsto_mean_of_tendsto_mean_sq_zero (a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k)
    (hsq : Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), (a k) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), a k) atTop (nhds 0) := by
  let b : ℕ → ℝ := fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
    ∑ k ∈ Finset.range (n + 1), a k
  let c : ℕ → ℝ := fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
    ∑ k ∈ Finset.range (n + 1), (a k) ^ 2
  have hbnonneg : ∀ n, 0 ≤ b n := by
    intro n
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k hk ↦ ha k)
  have hbc : ∀ n, (b n) ^ 2 ≤ c n := by
    intro n
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1))
      (f := a)
    rw [Finset.card_range] at hcs
    dsimp only [b, c]
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    calc
      ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ k ∈ Finset.range (n + 1), a k) ^ 2 =
          ((((n + 1 : ℕ) : ℝ))⁻¹) ^ 2 *
            (∑ k ∈ Finset.range (n + 1), a k) ^ 2 := by ring
      _ ≤ ((((n + 1 : ℕ) : ℝ))⁻¹) ^ 2 *
            ((n + 1 : ℕ) * ∑ k ∈ Finset.range (n + 1), (a k) ^ 2) := by
          gcongr
      _ = (((n + 1 : ℕ) : ℝ))⁻¹ *
            ∑ k ∈ Finset.range (n + 1), (a k) ^ 2 := by
          field_simp
  have hsq' : Tendsto (fun n ↦ (b n) ^ 2) atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ sq_nonneg (b n)) hbc
    simpa only [c] using hsq
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq'
  have heq : (fun n ↦ √((b n) ^ 2)) = b := by
    funext n
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hbnonneg n)]
  change Tendsto (fun n ↦ √((b n) ^ 2)) atTop (nhds √(0 : ℝ)) at hsqrt
  rw [heq, Real.sqrt_zero] at hsqrt
  simpa only [b] using hsqrt

theorem tendsto_birkhoffAverage_zero_of_correlation_dominated
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : K →L[ℂ] K) (hA : ‖A‖ ≤ 1) (w : K)
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hasq : Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), (a k) ^ 2) atTop (nhds 0))
    (C : ℝ) (_hC : 0 ≤ C)
    (hcorr : ∀ k, ‖⟪w, (A ^ k) w⟫_ℂ‖ ≤ C * a k) :
    Tendsto (fun n ↦ birkhoffAverage ℂ A id (n + 1) w) atTop (nhds 0) := by
  have hamean := tendsto_mean_of_tendsto_mean_sq_zero a ha hasq
  have hCmean : Tendsto (fun n ↦ C * ((((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), a k)) atTop (nhds 0) := by
    simpa using hamean.const_mul C
  have hmean : Tendsto (fun n ↦ (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n + 1), ‖⟪w, (A ^ k) w⟫_ℂ‖)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k hk ↦ norm_nonneg _)
    · intro n
      calc
        (((n + 1 : ℕ) : ℝ))⁻¹ *
            ∑ k ∈ Finset.range (n + 1), ‖⟪w, (A ^ k) w⟫_ℂ‖ ≤
            (((n + 1 : ℕ) : ℝ))⁻¹ *
              ∑ k ∈ Finset.range (n + 1), C * a k := by
          gcongr with k hk
          exact hcorr k
        _ = C * ((((n + 1 : ℕ) : ℝ))⁻¹ *
              ∑ k ∈ Finset.range (n + 1), a k) := by
          rw [← Finset.mul_sum]
          ring
    · exact hCmean
  exact tendsto_birkhoffAverage_zero_of_correlationMean_zero A hA w hmean

end Spectral
end Erdos656


namespace Erdos656

open Filter Function Set Topology MeasureTheory
open scoped ENNReal Pointwise Topology ComplexConjugate

noncomputable section

/-- The number of elements of `A` in `{0, ..., N - 1}`. -/
def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range N).filter (· ∈ A)).card

/-- The ordinary upper asymptotic density of a set of natural numbers. -/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countIn A N : ℝ) / N) Filter.atTop

/-- A set of naturals has positive ordinary upper asymptotic density. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

/-- Prefix densities are bounded below. -/
theorem isBoundedUnder_ge_prefixDensity (A : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => (countIn A N : ℝ) / N) := by
  exact isBoundedUnder_of
    ⟨0, fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

/-- Prefix densities are bounded above by one. -/
theorem isBoundedUnder_le_prefixDensity (A : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => (countIn A N : ℝ) / N) := by
  classical
  refine isBoundedUnder_of ⟨1, fun N => ?_⟩
  have hcount : countIn A N ≤ N := by
    simpa [countIn] using
      (Finset.card_le_card (Finset.filter_subset (fun n => n ∈ A) (Finset.range N)))
  exact div_le_one_of_le₀
    (Nat.cast_le.2 hcount)
    (Nat.cast_nonneg _)

/-- Every level strictly below the upper density is exceeded at arbitrarily
large prefix lengths. -/
theorem frequently_lt_prefixDensity {A : Set ℕ} {ε : ℝ}
    (hε : ε < upperDensity A) :
    ∃ᶠ N in atTop, ε < (countIn A N : ℝ) / N := by
  exact frequently_lt_of_lt_limsup
    (isBoundedUnder_ge_prefixDensity A).isCoboundedUnder_le hε

/-- Positive upper density supplies a strictly increasing sequence of positive
prefix lengths on which one fixed positive density lower bound holds. -/
theorem exists_positiveDensity_subsequence {A : Set ℕ}
    (hA : HasPositiveUpperDensity A) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ → ℕ, StrictMono N ∧
      ∀ k, ε < (countIn A (N k) : ℝ) / N k := by
  let ε := upperDensity A / 2
  have hεpos : 0 < ε := half_pos hA
  have hdpos : 0 < upperDensity A := hA
  have hεlt : ε < upperDensity A := by
    dsimp [ε]
    linarith [hdpos]
  obtain ⟨N, hNmono, hN⟩ :=
    extraction_of_frequently_atTop (frequently_lt_prefixDensity hεlt)
  exact ⟨ε, hεpos, N, hNmono, hN⟩

/-- The exact translated restricted-pair-sum conclusion of Erdős Problem 656.

Writing the target in `ℤ` records that the shift is an integer without using
truncated subtraction on naturals. -/
def HasTranslatedRestrictedPairSums (A B : Set ℕ) : Prop :=
  ∃ t : ℤ, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
    ∃ a ∈ A, (a : ℤ) = (b₁ : ℤ) + b₂ + t

/-- Return times of `x` to `U` under the iterates of `T`. -/
def returnTimes {X : Type*} (T : X → X) (x : X) (U : Set X) : Set ℕ :=
  {n | T^[n] x ∈ U}

/-! ### The pointed symbolic system used by the correspondence principle -/

/-- The two-sided binary full shift. -/
abbrev SymbolicSpace := ℤ → Bool

/-- The point coding a set of naturals, extended by `false` at negative
coordinates. -/
def symbolicPoint (A : Set ℕ) : SymbolicSpace := fun z =>
  by
    classical
    exact if 0 ≤ z then decide (z.toNat ∈ A) else false

/-- The left shift on the binary full shift. -/
def symbolicShift (x : SymbolicSpace) : SymbolicSpace := fun z => x (z + 1)

/-- The cylinder detecting membership at coordinate zero. -/
def originCylinder : Set SymbolicSpace := {x | x 0 = true}

@[simp] theorem symbolicShift_apply (x : SymbolicSpace) (z : ℤ) :
    symbolicShift x z = x (z + 1) := rfl

@[simp] theorem symbolicShift_iterate_apply (x : SymbolicSpace) (n : ℕ) (z : ℤ) :
    symbolicShift^[n] x z = x (z + n) := by
  induction n generalizing x z with
  | zero => simp
  | succ n ih =>
      simp only [Function.iterate_succ_apply]
      rw [ih]
      simp only [symbolicShift_apply]
      congr 1
      push_cast
      ring

theorem continuous_symbolicShift : Continuous symbolicShift := by
  exact continuous_pi fun z => continuous_apply (z + 1)

/-- The shift is a homeomorphism, as required by the KMRR dynamical theorem. -/
def symbolicShiftHomeomorph : SymbolicSpace ≃ₜ SymbolicSpace where
  toFun := symbolicShift
  invFun := fun x z => x (z - 1)
  left_inv x := by
    funext z
    simp [symbolicShift]
  right_inv x := by
    funext z
    simp [symbolicShift]
  continuous_toFun := continuous_symbolicShift
  continuous_invFun := continuous_pi fun z => continuous_apply (z - 1)

/-- The origin cylinder is clopen. -/
theorem isClopen_originCylinder : IsClopen originCylinder := by
  change IsClopen ((fun x : SymbolicSpace => x 0) ⁻¹' {true})
  exact IsClopen.preimage (isClopen_discrete {true}) (continuous_apply 0)

/-- The symbolic return-time set is literally the original set; no
correspondence inequality is lost at this stage. -/
theorem returnTimes_symbolicPoint (A : Set ℕ) :
    returnTimes symbolicShift (symbolicPoint A) originCylinder = A := by
  ext n
  simp [returnTimes, originCylinder, symbolicPoint]

/-- The uniform probability measure on the first `N + 1` points of the
symbolic orbit. -/
noncomputable def empiricalMeasure (A : Set ℕ) (N : ℕ) :
    MeasureTheory.ProbabilityMeasure SymbolicSpace := by
  let u : PMF ℕ := PMF.uniformOfFinset (Finset.range (N + 1)) (by simp)
  let q : PMF SymbolicSpace :=
    u.map fun n => symbolicShift^[n] (symbolicPoint A)
  exact ⟨q.toMeasure, inferInstance⟩

/-- Integrating against an empirical orbit measure is the corresponding
finite orbit average. -/
theorem integral_empiricalMeasure (A : Set ℕ) (N : ℕ)
    (f : BoundedContinuousFunction SymbolicSpace ℝ) :
    ∫ x, f x ∂(empiricalMeasure A N : Measure SymbolicSpace) =
      ((N + 1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.range (N + 1), f (symbolicShift^[n] (symbolicPoint A)) := by
  classical
  change ∫ x, f x ∂(((PMF.uniformOfFinset (Finset.range (N + 1)) (by simp)).map
    (fun n => symbolicShift^[n] (symbolicPoint A))).toMeasure) = _
  rw [← PMF.toMeasure_map (fun n => symbolicShift^[n] (symbolicPoint A))
    (PMF.uniformOfFinset (Finset.range (N + 1)) (by simp))
    (measurable_of_countable _)]
  rw [integral_map]
  · have hint : Integrable
        (fun n => f (symbolicShift^[n] (symbolicPoint A)))
        (PMF.uniformOfFinset (Finset.range (N + 1)) (by simp)).toMeasure := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ‖f‖
      exact ae_of_all _ fun n => f.norm_coe_le_norm _
    rw [PMF.integral_eq_tsum _ _ hint]
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : n ≤ N := by simpa using hn
      simp [PMF.uniformOfFinset_apply, hnle, ENNReal.toReal_inv,
        ENNReal.toReal_add]
    · intro n hn
      have hn' : N < n := by simpa using hn
      have hnnot : ¬n ≤ N := Nat.not_le.mpr hn'
      simp [PMF.uniformOfFinset_apply, hnnot]
  · exact (measurable_of_countable _).aemeasurable
  · exact f.continuous.aestronglyMeasurable

/-- The mass assigned by the orbit empirical measure to the origin cylinder
is exactly the corresponding prefix density. -/
theorem empiricalMeasure_originCylinder (A : Set ℕ) (N : ℕ) :
    empiricalMeasure A N originCylinder =
      (countIn A (N + 1) : NNReal) / (N + 1) := by
  classical
  change ENNReal.toNNReal
      (((PMF.uniformOfFinset (Finset.range (N + 1)) (by simp)).map
        (fun n => symbolicShift^[n] (symbolicPoint A))).toMeasure originCylinder) = _
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _)
    isClopen_originCylinder.isOpen.measurableSet]
  rw [PMF.toMeasure_uniformOfFinset_apply _ _
    (Set.countable_univ.mono (Set.subset_univ _)).measurableSet]
  simp [ENNReal.toNNReal_div, ENNReal.toNNReal_add, countIn,
    originCylinder, symbolicPoint]

/-- Compactness supplies a weak cluster point of the empirical orbit
measures.  This is the first compactness step in the pointed Furstenberg
correspondence principle. -/
theorem exists_empiricalMeasure_cluster (A : Set ℕ) :
    ∃ μ : MeasureTheory.ProbabilityMeasure SymbolicSpace,
      MapClusterPt μ atTop (empiricalMeasure A) := by
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (empiricalMeasure A) atTop)
  exact ⟨μ, hμ⟩

/-- A positive-density set has a weak limit of prefix-orbit empirical
measures which gives positive mass to the origin cylinder. -/
theorem exists_positive_empirical_limit {A : Set ℕ}
    (hA : HasPositiveUpperDensity A) :
    ∃ μ : MeasureTheory.ProbabilityMeasure SymbolicSpace,
      0 < μ originCylinder ∧
      ∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun k => empiricalMeasure A (N k - 1)) atTop (𝓝 μ) := by
  obtain ⟨ε, hεpos, N₀, hN₀mono, hN₀density⟩ :=
    exists_positiveDensity_subsequence hA
  have hN₀pos (k : ℕ) : 0 < N₀ k := by
    by_contra hk
    have hk0 : N₀ k = 0 := Nat.eq_zero_of_not_pos hk
    have hd := hN₀density k
    simp [hk0] at hd
    linarith
  let μs : ℕ → MeasureTheory.ProbabilityMeasure SymbolicSpace :=
    fun k => empiricalMeasure A (N₀ k - 1)
  obtain ⟨μ, φ, hφmono, hφlim⟩ := CompactSpace.tendsto_subseq μs
  let N : ℕ → ℕ := N₀ ∘ φ
  have hNmono : StrictMono N := hN₀mono.comp hφmono
  have hlim : Tendsto (fun k => empiricalMeasure A (N k - 1)) atTop (𝓝 μ) := by
    simpa [μs, N, Function.comp_def] using hφlim
  have hmass : Tendsto
      (fun k => empiricalMeasure A (N k - 1) originCylinder)
      atTop (𝓝 (μ originCylinder)) :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      hlim isClopen_originCylinder
  let εnn : NNReal := ⟨ε, hεpos.le⟩
  have hmassLower (k : ℕ) :
      εnn < empiricalMeasure A (N k - 1) originCylinder := by
    rw [empiricalMeasure_originCylinder]
    have hNkpos : 0 < N k := hN₀pos (φ k)
    change εnn < (countIn A (N k - 1 + 1) : NNReal) /
      (((N k - 1 : ℕ) : NNReal) + 1)
    have hnat : N k - 1 + 1 = N k := Nat.sub_add_cancel hNkpos
    have hden : ((N k - 1 : ℕ) : NNReal) + 1 = (N k : NNReal) := by
      exact_mod_cast hnat
    rw [hnat, hden]
    dsimp [εnn, N]
    exact_mod_cast hN₀density (φ k)
  have hεle : εnn ≤ μ originCylinder :=
    ge_of_tendsto hmass (Eventually.of_forall fun k => (hmassLower k).le)
  refine ⟨μ, lt_of_lt_of_le ?_ hεle, N, hNmono, hlim⟩
  exact hεpos

/-- Every weak limit of prefix-orbit empirical measures is invariant under
the symbolic shift.  The boundary error is the difference of two endpoint
values divided by the block length. -/
theorem empirical_limit_measurePreserving (A : Set ℕ)
    (μ : ProbabilityMeasure SymbolicSpace) (N : ℕ → ℕ)
    (hN : StrictMono N)
    (hlim : Tendsto (fun k => empiricalMeasure A (N k - 1)) atTop (𝓝 μ)) :
    MeasurePreserving symbolicShift (μ : Measure SymbolicSpace) μ := by
  let L : ℕ → ℕ := fun k => N k - 1 + 1
  have hLtop : Tendsto L atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (show N ≤ᶠ[atTop] L from
        Eventually.of_forall (fun k => by dsimp [L]; omega))
      hN.tendsto_atTop
  have hinv : Tendsto (fun k => ((L k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hLtop)
  have hsame : Tendsto
      (fun k => (empiricalMeasure A (N k - 1)).map
        symbolicShift)
      atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have horig :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
    let g : ℕ → ℝ := fun n => f (symbolicShift^[n] (symbolicPoint A))
    have hboundary : Tendsto
        (fun k => ((L k : ℝ))⁻¹ * (g (L k) - g 0)) atTop (𝓝 0) := by
      have hbound : ∀ k, ‖g (L k) - g 0‖ ≤ 2 * ‖f‖ := by
        intro k
        calc
          ‖g (L k) - g 0‖ ≤ ‖g (L k)‖ + ‖g 0‖ := norm_sub_le _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
          _ = 2 * ‖f‖ := by ring
      have hmajor : Tendsto (fun k => ((L k : ℝ))⁻¹ * (2 * ‖f‖)) atTop (𝓝 0) := by
        simpa using hinv.mul_const (2 * ‖f‖)
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      refine squeeze_zero'
        (f := fun k => ‖((L k : ℝ))⁻¹ * (g (L k) - g 0)‖)
        (g := fun k => ((L k : ℝ))⁻¹ * (2 * ‖f‖)) ?_ ?_ hmajor
      · exact Eventually.of_forall fun k => norm_nonneg _
      · exact Eventually.of_forall fun k => by
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
          exact mul_le_mul_of_nonneg_left (hbound k)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hidentity (k : ℕ) :
        ∫ x, f x ∂((empiricalMeasure A (N k - 1)).map
            symbolicShift : Measure SymbolicSpace) =
          ∫ x, f x ∂(empiricalMeasure A (N k - 1) : Measure SymbolicSpace) +
            ((L k : ℝ))⁻¹ * (g (L k) - g 0) := by
      change ∫ x, f x ∂Measure.map symbolicShift
          (empiricalMeasure A (N k - 1) : Measure SymbolicSpace) = _
      rw [integral_map continuous_symbolicShift.measurable.aemeasurable
        f.continuous.aestronglyMeasurable]
      change ∫ x, (f.compContinuous
          ⟨symbolicShift, continuous_symbolicShift⟩) x
          ∂(empiricalMeasure A (N k - 1) : Measure SymbolicSpace) = _
      rw [integral_empiricalMeasure A (N k - 1)
        (f.compContinuous ⟨symbolicShift, continuous_symbolicShift⟩)]
      rw [integral_empiricalMeasure]
      have htel :
          (∑ n ∈ Finset.range (L k), g (n + 1)) =
            (∑ n ∈ Finset.range (L k), g n) + (g (L k) - g 0) := by
        have hfirst := Finset.sum_range_succ' g (L k)
        have hlast := Finset.sum_range_succ g (L k)
        linarith
      change ((N k - 1 + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N k - 1 + 1),
            f (symbolicShift (symbolicShift^[n] (symbolicPoint A))) = _
      change _ = ((N k - 1 + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N k - 1 + 1), g n +
            ((N k - 1 + 1 : ℕ) : ℝ)⁻¹ *
              (g (N k - 1 + 1) - g 0)
      rw [show (∑ n ∈ Finset.range (N k - 1 + 1),
          f (symbolicShift (symbolicShift^[n] (symbolicPoint A)))) =
          ∑ n ∈ Finset.range (N k - 1 + 1), g (n + 1) by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [g, Function.iterate_succ_apply']]
      rw [htel]
      ring
    rw [show (fun k => ∫ x, f x ∂((empiricalMeasure A (N k - 1)).map
        symbolicShift : Measure SymbolicSpace)) =
        fun k => ∫ x, f x ∂(empiricalMeasure A (N k - 1) : Measure SymbolicSpace) +
          ((L k : ℝ))⁻¹ * (g (L k) - g 0) by funext k; exact hidentity k]
    simpa using horig.add hboundary
  have hmaplim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k => empiricalMeasure A (N k - 1)) μ hlim continuous_symbolicShift
  have heq : μ.map symbolicShift = μ :=
    tendsto_nhds_unique hmaplim hsame
  refine ⟨continuous_symbolicShift.measurable, ?_⟩
  exact congrArg ProbabilityMeasure.toMeasure heq

/-! ### Measures carried by the pointed symbolic orbit closure -/

/-- The closure of the forward symbolic orbit of the point which codes `A`. -/
def orbitClosure (A : Set ℕ) : Set SymbolicSpace :=
  closure (Set.range fun n : ℕ => symbolicShift^[n] (symbolicPoint A))

theorem isCompact_orbitClosure (A : Set ℕ) :
    IsCompact (orbitClosure A) :=
  isClosed_closure.isCompact

/-- Probability measures which give no mass to the complement of the
forward orbit closure.  This is the closed support condition which prevents
the ergodic-selection step from losing the original coding point. -/
def carriedProbabilities (A : Set ℕ) :
    Set (ProbabilityMeasure SymbolicSpace) :=
  {ν | ν (orbitClosure A)ᶜ = 0}

theorem isClosed_carriedProbabilities (A : Set ℕ) :
    IsClosed (carriedProbabilities A) := by
  let S : Set (FiniteMeasure SymbolicSpace) :=
    {ν | ν.mass ≤ 1 ∧ ν (orbitClosure A)ᶜ = 0}
  have hScompact : IsCompact S :=
    isCompact_setOfPred_finiteMeasure_le_of_isCompact 1
      (isCompact_orbitClosure A)
  have hpre : carriedProbabilities A =
      ProbabilityMeasure.toFiniteMeasure ⁻¹' S := by
    ext ν
    change ν (orbitClosure A)ᶜ = 0 ↔
      ν.toFiniteMeasure.mass ≤ 1 ∧
        ν.toFiniteMeasure (orbitClosure A)ᶜ = 0
    rw [ν.mass_toFiniteMeasure]
    simp only [le_refl, true_and, ProbabilityMeasure.toFiniteMeasure_apply]
  rw [hpre]
  exact hScompact.isClosed.preimage ProbabilityMeasure.toFiniteMeasure_continuous

theorem isCompact_carriedProbabilities (A : Set ℕ) :
    IsCompact (carriedProbabilities A) :=
  (isClosed_carriedProbabilities A).isCompact

theorem empiricalMeasure_mem_carriedProbabilities (A : Set ℕ) (N : ℕ) :
    empiricalMeasure A N ∈ carriedProbabilities A := by
  rw [carriedProbabilities]
  change empiricalMeasure A N (orbitClosure A)ᶜ = 0
  rw [← ENNReal.coe_eq_zero,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  have hae : ∀ᵐ x ∂(empiricalMeasure A N : Measure SymbolicSpace),
      x ∈ orbitClosure A := by
    classical
    change ∀ᵐ x ∂(((PMF.uniformOfFinset (Finset.range (N + 1)) (by simp)).map
      (fun n => symbolicShift^[n] (symbolicPoint A))).toMeasure),
        x ∈ orbitClosure A
    rw [← PMF.toMeasure_map (fun n => symbolicShift^[n] (symbolicPoint A))
      (PMF.uniformOfFinset (Finset.range (N + 1)) (by simp))
      (measurable_of_countable _)]
    apply (ae_map_iff (measurable_of_countable _).aemeasurable
      (show MeasurableSet {x | x ∈ orbitClosure A} from
        isClosed_closure.measurableSet)).2
    exact ae_of_all _ fun n => subset_closure (Set.mem_range_self n)
  rw [← mem_ae_iff]
  filter_upwards [hae] with x hx
  simpa using hx

/-- The orbit-carried condition survives weak limits of empirical orbit
measures.  The proof is the open-set half of Portmanteau applied to the
complement of the closed orbit closure. -/
theorem empirical_limit_mem_carriedProbabilities (A : Set ℕ)
    (μ : ProbabilityMeasure SymbolicSpace) (N : ℕ → ℕ)
    (hlim : Tendsto (fun k => empiricalMeasure A (N k - 1)) atTop (𝓝 μ)) :
    μ ∈ carriedProbabilities A := by
  have hopen : IsOpen (orbitClosure A)ᶜ := isClosed_closure.isOpen_compl
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hopen
  have hzero : (fun k => (empiricalMeasure A (N k - 1) :
      Measure SymbolicSpace) (orbitClosure A)ᶜ) = fun _ => 0 := by
    funext k
    have hm := empiricalMeasure_mem_carriedProbabilities A (N k - 1)
    change empiricalMeasure A (N k - 1) (orbitClosure A)ᶜ = 0 at hm
    rw [← ENNReal.coe_eq_zero,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hm
    exact hm
  rw [hzero, liminf_const] at hle
  rw [carriedProbabilities]
  change μ (orbitClosure A)ᶜ = 0
  rw [← ENNReal.coe_eq_zero]
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact bot_unique hle

/-- A measure carried by the forward orbit closure has topological support
contained in that closure. -/
theorem support_subset_orbitClosure_of_mem_carried {A : Set ℕ}
    {ν : ProbabilityMeasure SymbolicSpace}
    (hν : ν ∈ carriedProbabilities A) :
    (ν : Measure SymbolicSpace).support ⊆ orbitClosure A := by
  apply Measure.support_subset_of_isClosed isClosed_closure
  rw [mem_ae_iff]
  have h := hν
  change ν (orbitClosure A)ᶜ = 0 at h
  rw [← ENNReal.coe_eq_zero,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact h

/-! ### Ergodic selection from extreme invariant measures -/

/-- A probability measure is embedded in a real product space by all of its
bounded-continuous moments.  This ambient space is locally convex, so the
Krein--Milman theorem applies to compact sets of such moment vectors. -/
def probabilityMoments (ν : ProbabilityMeasure SymbolicSpace) :
    BoundedContinuousFunction SymbolicSpace ℝ → ℝ :=
  fun f => ∫ x, f x ∂(ν : Measure SymbolicSpace)

theorem continuous_probabilityMoments : Continuous probabilityMoments := by
  exact continuous_pi fun f =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

theorem injective_probabilityMoments : Injective probabilityMoments := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact congrFun h f

/-- The compact set of shift-invariant probability measures carried by the
forward orbit closure of the coding point for `A`. -/
def invariantProbabilities (A : Set ℕ) :
    Set (ProbabilityMeasure SymbolicSpace) :=
  {ν | ν.map symbolicShift = ν} ∩
    carriedProbabilities A

theorem isClosed_invariantProbabilities (A : Set ℕ) :
    IsClosed (invariantProbabilities A) := by
  exact (isClosed_eq
    (ProbabilityMeasure.continuous_map continuous_symbolicShift)
    continuous_id).inter (isClosed_carriedProbabilities A)

theorem isCompact_invariantProbabilities (A : Set ℕ) :
    IsCompact (invariantProbabilities A) :=
  (isClosed_invariantProbabilities A).isCompact

/-- The mass of the origin cylinder, expressed as an integral so that its
continuity in the weak topology is immediate. -/
def originMassReal (ν : ProbabilityMeasure SymbolicSpace) : ℝ :=
  ∫ x, BoundedContinuousFunction.indicator originCylinder
    isClopen_originCylinder x ∂(ν : Measure SymbolicSpace)

theorem continuous_originMassReal : Continuous originMassReal :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction _

theorem originMassReal_eq (ν : ProbabilityMeasure SymbolicSpace) :
    originMassReal ν = (ν : Measure SymbolicSpace).real originCylinder := by
  rw [originMassReal]
  exact integral_indicator_one
    isClopen_originCylinder.isOpen.measurableSet

theorem exists_maximizingInvariantProbability
    (A : Set ℕ)
    (ν₀ : ProbabilityMeasure SymbolicSpace)
    (hν₀ : ν₀ ∈ invariantProbabilities A) :
    ∃ ν ∈ invariantProbabilities A,
      ∀ ρ ∈ invariantProbabilities A, originMassReal ρ ≤ originMassReal ν := by
  obtain ⟨ν, hν, hmax⟩ :=
    (isCompact_invariantProbabilities A).exists_isMaxOn
      ⟨ν₀, hν₀⟩ continuous_originMassReal.continuousOn
  exact ⟨ν, hν, hmax⟩

/-- The compact face consisting of invariant probabilities that maximize
the origin-cylinder mass. -/
def maximizingInvariantProbabilities (A : Set ℕ) :
    Set (ProbabilityMeasure SymbolicSpace) :=
  {ν | ν ∈ invariantProbabilities A ∧
    ∀ ρ ∈ invariantProbabilities A, originMassReal ρ ≤ originMassReal ν}

theorem isClosed_maximizingInvariantProbabilities (A : Set ℕ) :
    IsClosed (maximizingInvariantProbabilities A) := by
  rw [maximizingInvariantProbabilities]
  apply (isClosed_invariantProbabilities A).inter
  have hclosed : IsClosed (⋂ ρ ∈ invariantProbabilities A,
      originMassReal ⁻¹' Set.Ici (originMassReal ρ)) :=
    isClosed_biInter fun ρ hρ =>
      isClosed_Ici.preimage continuous_originMassReal
  have heq :
      { ν : ProbabilityMeasure SymbolicSpace |
        ∀ ρ ∈ invariantProbabilities A, originMassReal ρ ≤ originMassReal ν } =
        ⋂ ρ ∈ invariantProbabilities A,
          originMassReal ⁻¹' Set.Ici (originMassReal ρ) := by
    ext ν
    simp
  change IsClosed
    ({ ν : ProbabilityMeasure SymbolicSpace |
      ∀ ρ ∈ invariantProbabilities A, originMassReal ρ ≤ originMassReal ν } :
      Set (ProbabilityMeasure SymbolicSpace))
  rw [heq]
  exact hclosed

theorem isCompact_maximizingInvariantProbabilities (A : Set ℕ) :
    IsCompact (maximizingInvariantProbabilities A) :=
  (isClosed_maximizingInvariantProbabilities A).isCompact

theorem nonempty_maximizingInvariantProbabilities
    (A : Set ℕ)
    (ν₀ : ProbabilityMeasure SymbolicSpace)
    (hν₀ : ν₀ ∈ invariantProbabilities A) :
    (maximizingInvariantProbabilities A).Nonempty := by
  obtain ⟨ν, hν, hmax⟩ := exists_maximizingInvariantProbability A ν₀ hν₀
  exact ⟨ν, hν, hmax⟩

/-- Krein--Milman supplies an extreme point of the maximizing face after
embedding probabilities by their bounded-continuous moments. -/
theorem exists_extreme_maximizingInvariantProbability
    (A : Set ℕ)
    (ν₀ : ProbabilityMeasure SymbolicSpace)
    (hν₀ : ν₀ ∈ invariantProbabilities A) :
    ∃ ν ∈ maximizingInvariantProbabilities A,
      probabilityMoments ν ∈ Set.extremePoints ℝ
        (probabilityMoments '' maximizingInvariantProbabilities A) := by
  let S := probabilityMoments '' maximizingInvariantProbabilities A
  have hScompact : IsCompact S :=
    (isCompact_maximizingInvariantProbabilities A).image
      continuous_probabilityMoments
  have hSne : S.Nonempty :=
    (nonempty_maximizingInvariantProbabilities A ν₀ hν₀).image _
  obtain ⟨φ, hφ⟩ := hScompact.extremePoints_nonempty hSne
  obtain ⟨ν, hν, rfl⟩ := hφ.1
  exact ⟨ν, hν, hφ⟩

theorem measurePreserving_of_mem_invariantProbabilities
    (A : Set ℕ)
    (ν : ProbabilityMeasure SymbolicSpace)
    (hν : ν ∈ invariantProbabilities A) :
    MeasurePreserving symbolicShift (ν : Measure SymbolicSpace) ν := by
  refine ⟨continuous_symbolicShift.measurable, ?_⟩
  exact congrArg ProbabilityMeasure.toMeasure hν.1

theorem conditional_mem_invariantProbabilities
    (A : Set ℕ)
    (ν : ProbabilityMeasure SymbolicSpace)
    (hν : ν ∈ invariantProbabilities A) {s : Set SymbolicSpace}
    (hsm : MeasurableSet s) (hpre : symbolicShift ⁻¹' s = s)
    (hs : (ν : Measure SymbolicSpace) s ≠ 0) :
    let νs : ProbabilityMeasure SymbolicSpace :=
      ⟨ProbabilityTheory.cond (ν : Measure SymbolicSpace) s,
        ProbabilityTheory.cond_isProbabilityMeasure hs⟩
    νs ∈ invariantProbabilities A := by
  let νs : ProbabilityMeasure SymbolicSpace :=
    ⟨ProbabilityTheory.cond (ν : Measure SymbolicSpace) s,
      ProbabilityTheory.cond_isProbabilityMeasure hs⟩
  have hT := measurePreserving_of_mem_invariantProbabilities A ν hν
  have hres : MeasurePreserving symbolicShift
      ((ν : Measure SymbolicSpace).restrict s)
      ((ν : Measure SymbolicSpace).restrict s) := by
    convert hT.restrict_preimage hsm
    exact hpre.symm
  have hcond : MeasurePreserving symbolicShift
      (ProbabilityTheory.cond (ν : Measure SymbolicSpace) s)
      (ProbabilityTheory.cond (ν : Measure SymbolicSpace) s) := by
    simpa only [ProbabilityTheory.cond] using
      hres.smul_measure ((ν : Measure SymbolicSpace) s)⁻¹
  constructor
  · apply ProbabilityMeasure.toMeasure_injective
    exact hcond.map_eq
  · rw [carriedProbabilities]
    change νs (orbitClosure A)ᶜ = 0
    rw [← ENNReal.coe_eq_zero,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    apply ProbabilityTheory.cond_absolutelyContinuous
    have hcarried := hν.2
    change ν (orbitClosure A)ᶜ = 0 at hcarried
    rw [← ENNReal.coe_eq_zero,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hcarried
    exact hcarried

noncomputable def conditionedProbability
    (ν : ProbabilityMeasure SymbolicSpace) (s : Set SymbolicSpace)
    (hs : (ν : Measure SymbolicSpace) s ≠ 0) :
    ProbabilityMeasure SymbolicSpace :=
  ⟨ProbabilityTheory.cond (ν : Measure SymbolicSpace) s,
    ProbabilityTheory.cond_isProbabilityMeasure hs⟩

@[simp] theorem coe_conditionedProbability
    (ν : ProbabilityMeasure SymbolicSpace) (s : Set SymbolicSpace)
    (hs : (ν : Measure SymbolicSpace) s ≠ 0) :
    (conditionedProbability ν s hs : Measure SymbolicSpace) =
      ProbabilityTheory.cond (ν : Measure SymbolicSpace) s := rfl

/-- The law of total probability, transferred to the real moment embedding. -/
theorem probabilityMoments_conditioned_add_compl
    (ν : ProbabilityMeasure SymbolicSpace) {s : Set SymbolicSpace}
    (hsm : MeasurableSet s) (hs : (ν : Measure SymbolicSpace) s ≠ 0)
    (hsc : (ν : Measure SymbolicSpace) sᶜ ≠ 0) :
    ((ν : Measure SymbolicSpace) s).toReal •
          probabilityMoments (conditionedProbability ν s hs) +
        ((ν : Measure SymbolicSpace) sᶜ).toReal •
          probabilityMoments (conditionedProbability ν sᶜ hsc) =
      probabilityMoments ν := by
  have hmeasure :
      (ν : Measure SymbolicSpace) s •
          (conditionedProbability ν s hs : Measure SymbolicSpace) +
        (ν : Measure SymbolicSpace) sᶜ •
          (conditionedProbability ν sᶜ hsc : Measure SymbolicSpace) =
      (ν : Measure SymbolicSpace) := by
    ext t ht
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      coe_conditionedProbability]
    simpa only [mul_comm] using
      (ProbabilityTheory.cond_add_cond_compl_eq hsm
        (ν : Measure SymbolicSpace) (t := t))
  funext f
  let : IsFiniteMeasure
      ((ν : Measure SymbolicSpace) s •
        (conditionedProbability ν s hs : Measure SymbolicSpace)) :=
    ⟨by
      rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      exact measure_lt_top (ν : Measure SymbolicSpace) s⟩
  let : IsFiniteMeasure
      ((ν : Measure SymbolicSpace) sᶜ •
        (conditionedProbability ν sᶜ hsc : Measure SymbolicSpace)) :=
    ⟨by
      rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      exact measure_lt_top (ν : Measure SymbolicSpace) sᶜ⟩
  have hi := congrArg
    (fun ρ : Measure SymbolicSpace => ∫ x, f x ∂ρ) hmeasure
  rw [integral_add_measure
      (f.integrable _)
      (f.integrable _),
    integral_smul_measure, integral_smul_measure] at hi
  simpa only [probabilityMoments, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] using hi

/-- An extreme point of the maximizing face is ergodic.  If an invariant
set had both it and its complement of positive mass, conditioning on the two
pieces would give a nontrivial real open-segment decomposition inside that
face, contradicting extremality. -/
theorem ergodic_of_extreme_maximizingInvariantProbability
    (A : Set ℕ)
    (ν : ProbabilityMeasure SymbolicSpace)
    (hν : ν ∈ maximizingInvariantProbabilities A)
    (hext : probabilityMoments ν ∈ Set.extremePoints ℝ
      (probabilityMoments '' maximizingInvariantProbabilities A)) :
    Ergodic symbolicShift (ν : Measure SymbolicSpace) := by
  have hT := measurePreserving_of_mem_invariantProbabilities A ν hν.1
  refine ⟨hT, ⟨?_⟩⟩
  intro s hsm hpre
  by_contra H
  obtain ⟨hs, hsc⟩ :
      (ν : Measure SymbolicSpace) s ≠ 0 ∧
        (ν : Measure SymbolicSpace) sᶜ ≠ 0 := by
    simpa [eventuallyEmptyOrUniv_iff, ae_iff, and_comm] using! H
  let νs : ProbabilityMeasure SymbolicSpace :=
    conditionedProbability ν s hs
  let νc : ProbabilityMeasure SymbolicSpace :=
    conditionedProbability ν sᶜ hsc
  have hνsInv : νs ∈ invariantProbabilities A := by
    simpa only [νs, conditionedProbability] using
      conditional_mem_invariantProbabilities A ν hν.1 hsm hpre hs
  have hνcInv : νc ∈ invariantProbabilities A := by
    simpa only [νc, conditionedProbability] using
      conditional_mem_invariantProbabilities A ν hν.1 hsm.compl
        (by rw [preimage_compl, hpre]) hsc
  let a : ℝ := ((ν : Measure SymbolicSpace) s).toReal
  let b : ℝ := ((ν : Measure SymbolicSpace) sᶜ).toReal
  have ha : 0 < a := by
    exact ENNReal.toReal_pos hs (measure_ne_top (ν : Measure SymbolicSpace) s)
  have hb : 0 < b := by
    exact ENNReal.toReal_pos hsc (measure_ne_top (ν : Measure SymbolicSpace) sᶜ)
  have hab : a + b = 1 := by
    have hadd := congrArg ENNReal.toReal
      (measure_add_measure_compl hsm :
        (ν : Measure SymbolicSpace) s +
          (ν : Measure SymbolicSpace) sᶜ = (ν : Measure SymbolicSpace) Set.univ)
    rw [ENNReal.toReal_add
      (measure_ne_top (ν : Measure SymbolicSpace) s)
      (measure_ne_top (ν : Measure SymbolicSpace) sᶜ),
      measure_univ, ENNReal.toReal_one] at hadd
    exact hadd
  have hdecomp :
      a • probabilityMoments νs + b • probabilityMoments νc =
        probabilityMoments ν := by
    simpa only [a, b, νs, νc] using
      probabilityMoments_conditioned_add_compl ν hsm hs hsc
  have horigin := congrFun hdecomp
    (BoundedContinuousFunction.indicator originCylinder
      isClopen_originCylinder)
  have horigin' :
      a * originMassReal νs + b * originMassReal νc =
        originMassReal ν := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      probabilityMoments, originMassReal] using horigin
  have hνsLe : originMassReal νs ≤ originMassReal ν :=
    hν.2 νs hνsInv
  have hνcLe : originMassReal νc ≤ originMassReal ν :=
    hν.2 νc hνcInv
  have hνsEq : originMassReal νs = originMassReal ν := by
    apply le_antisymm hνsLe
    by_contra hnot
    have hlt : originMassReal νs < originMassReal ν :=
      lt_of_not_ge hnot
    have halt : a * originMassReal νs < a * originMassReal ν :=
      mul_lt_mul_of_pos_left hlt ha
    have hble : b * originMassReal νc ≤ b * originMassReal ν :=
      mul_le_mul_of_nonneg_left hνcLe hb.le
    have hsumlt :
        a * originMassReal νs + b * originMassReal νc <
          a * originMassReal ν + b * originMassReal ν :=
      add_lt_add_of_lt_of_le halt hble
    have : originMassReal ν < originMassReal ν := by
      calc
        originMassReal ν =
            a * originMassReal νs + b * originMassReal νc :=
          horigin'.symm
        _ < a * originMassReal ν + b * originMassReal ν := hsumlt
        _ = (a + b) * originMassReal ν := by ring
        _ = originMassReal ν := by rw [hab, one_mul]
    exact this.false
  have hνcEq : originMassReal νc = originMassReal ν := by
    apply le_antisymm hνcLe
    by_contra hnot
    have hlt : originMassReal νc < originMassReal ν :=
      lt_of_not_ge hnot
    have hblt : b * originMassReal νc < b * originMassReal ν :=
      mul_lt_mul_of_pos_left hlt hb
    have hale : a * originMassReal νs ≤ a * originMassReal ν :=
      mul_le_mul_of_nonneg_left hνsLe ha.le
    have hsumlt :
        a * originMassReal νs + b * originMassReal νc <
          a * originMassReal ν + b * originMassReal ν :=
      add_lt_add_of_le_of_lt hale hblt
    have : originMassReal ν < originMassReal ν := by
      calc
        originMassReal ν =
            a * originMassReal νs + b * originMassReal νc :=
          horigin'.symm
        _ < a * originMassReal ν + b * originMassReal ν := hsumlt
        _ = (a + b) * originMassReal ν := by ring
        _ = originMassReal ν := by rw [hab, one_mul]
    exact this.false
  have hνsMax : νs ∈ maximizingInvariantProbabilities A := by
    refine ⟨hνsInv, ?_⟩
    intro ρ hρ
    rw [hνsEq]
    exact hν.2 ρ hρ
  have hνcMax : νc ∈ maximizingInvariantProbabilities A := by
    refine ⟨hνcInv, ?_⟩
    intro ρ hρ
    rw [hνcEq]
    exact hν.2 ρ hρ
  have hopen : probabilityMoments ν ∈
      openSegment ℝ (probabilityMoments νs) (probabilityMoments νc) := by
    exact ⟨a, b, ha, hb, hab, hdecomp⟩
  have hmom : probabilityMoments νs = probabilityMoments ν :=
    hext.2 ⟨νs, hνsMax, rfl⟩ ⟨νc, hνcMax, rfl⟩ hopen
  have hνsEqν : νs = ν := injective_probabilityMoments hmom
  have hmeasureEq : (νs : Measure SymbolicSpace) =
      (ν : Measure SymbolicSpace) :=
    congrArg ProbabilityMeasure.toMeasure hνsEqν
  rw [← hmeasureEq] at hsc
  simp [νs, conditionedProbability, ProbabilityTheory.cond_apply, hsm] at hsc

/-- Positive upper density supplies an ergodic invariant probability of
positive origin-cylinder mass whose support remains inside the forward
orbit closure of the original symbolic coding point. -/
theorem exists_carried_ergodic_probability {A : Set ℕ}
    (hA : HasPositiveUpperDensity A) :
    ∃ ν : ProbabilityMeasure SymbolicSpace,
      Ergodic symbolicShift (ν : Measure SymbolicSpace) ∧
        ν ∈ carriedProbabilities A ∧
          0 < (ν : Measure SymbolicSpace) originCylinder := by
  obtain ⟨μ, hμorigin, N, hN, hlim⟩ := exists_positive_empirical_limit hA
  have hmp := empirical_limit_measurePreserving A μ N hN hlim
  have hμinv : μ ∈ invariantProbabilities A := by
    constructor
    · apply ProbabilityMeasure.toMeasure_injective
      exact hmp.map_eq
    · exact empirical_limit_mem_carriedProbabilities A μ N hlim
  obtain ⟨ν, hνmax, hνext⟩ :=
    exists_extreme_maximizingInvariantProbability A μ hμinv
  have hνerg :=
    ergodic_of_extreme_maximizingInvariantProbability A ν hνmax hνext
  refine ⟨ν, hνerg, hνmax.1.2, ?_⟩
  have hμreal : 0 < originMassReal μ := by
    rw [originMassReal_eq, ProbabilityMeasure.measureReal_eq_coe_coeFn]
    exact_mod_cast hμorigin
  have hνreal : 0 < originMassReal ν :=
    hμreal.trans_le (hνmax.2 μ hμinv)
  rw [originMassReal_eq, Measure.real, ENNReal.toReal_pos_iff] at hνreal
  exact hνreal.1

/-! ### The mean-ergodic input for generic points -/

/-- The Koopman operator on real `L²` associated to a measure-preserving map. -/
def koopmanL2 {X : Type*} [MeasurableSpace X] (T : X → X)
    (μ : Measure X) (hT : MeasurePreserving T μ μ) :
    Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μ :=
  (Lp.compMeasurePreservingₗᵢ (p := (2 : ℝ≥0∞)) ℝ T hT).toContinuousLinearMap

/-- The Koopman operator is a contraction on `L²`. -/
theorem norm_koopmanL2_le_one {X : Type*} [MeasurableSpace X]
    (T : X → X) (μ : Measure X) (hT : MeasurePreserving T μ μ) :
    ‖koopmanL2 T μ hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [koopmanL2]

/-- In an ergodic probability system, the Hilbert-space mean ergodic
theorem identifies the `L²` limit of every continuous observable with the
constant equal to its integral. -/
theorem meanErgodic_limit_ae_const
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [CompactSpace X]
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (f : BoundedContinuousFunction X ℝ) :
    Tendsto
      (fun n ↦ birkhoffAverage ℝ (koopmanL2 T μ hT.1) id n
        (BoundedContinuousFunction.toLp 2 μ ℝ f))
      atTop
      (𝓝 (indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top μ Set.univ) (∫ x, f x ∂μ))) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let U := koopmanL2 T μ hT.1
  let v := BoundedContinuousFunction.toLp 2 μ ℝ f
  let S : Submodule ℝ (Lp ℝ 2 μ) :=
    (U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ).eqLocus
      (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let w : Lp ℝ 2 μ := S.orthogonalProjectionOnto v
  have hlim : Tendsto
      (fun n ↦ birkhoffAverage ℝ U id n v) atTop (𝓝 w) := by
    change Tendsto (fun n ↦ birkhoffAverage ℝ U id n v) atTop
      (𝓝 (S.starProjection v))
    rw [← S.coe_orthogonalProjectionOnto_apply v]
    simpa only [S] using U.tendsto_birkhoffAverage_orthogonalProjection
      (norm_koopmanL2_le_one T μ hT.1) v
  have hwfix : U w = w := by
    exact S.starProjection_apply_mem v
  have hwfix' : w.1.compMeasurePreserving T hT.1 = w.1 := by
    apply congrArg Subtype.val at hwfix
    simpa [U, koopmanL2] using hwfix
  obtain ⟨c, hc⟩ := hT.eq_const_of_compMeasurePreserving_eq hwfix'
  let wc : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top μ Set.univ) c
  let oneLp : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top μ Set.univ) (1 : ℝ)
  have hwc : w = wc := by
    apply Lp.ext
    have hc' : (w : X → ℝ) =ᵐ[μ] (fun _ ↦ c) := by
      rw [show w.1 = AEEqFun.const X c from hc]
      exact AEEqFun.coeFn_const X c
    exact hc'.trans (by
      simpa [wc] using
        (@indicatorConstLp_coeFn X ℝ _ 2 μ _ Set.univ
          MeasurableSet.univ (measure_ne_top μ Set.univ) c).symm)
  have honefix : U oneLp = oneLp := by
    apply Lp.ext
    have hcomp := oneLp.1.coeFn_compMeasurePreserving hT.1
    have hone := @indicatorConstLp_coeFn X ℝ _ 2 μ _ Set.univ
      MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℝ)
    filter_upwards [hcomp, hone, hT.1.quasiMeasurePreserving.ae hone] with x hx h1 h2
    simpa [U, koopmanL2, oneLp] using hx.trans (h2.trans h1.symm)
  let oneS : S := ⟨oneLp, honefix⟩
  have hinner : inner ℝ oneLp w = inner ℝ oneLp v := by
    change inner ℝ oneLp (S.starProjection v) = inner ℝ oneLp v
    rw [← S.coe_orthogonalProjectionOnto_apply v]
    exact S.inner_orthogonalProjectionOnto_eq_of_mem_left oneS v
  have hwc_ae : (wc : X → ℝ) =ᵐ[μ] (fun _ ↦ c) := by
    simpa [wc] using
      (@indicatorConstLp_coeFn X ℝ _ 2 μ _ Set.univ
        MeasurableSet.univ (measure_ne_top μ Set.univ) c)
  have hv_ae : (v : X → ℝ) =ᵐ[μ] f := by
    simpa [v] using f.coeFn_toLp 2 μ ℝ
  have hinner' : ∫ x, wc x ∂μ = ∫ x, v x ∂μ := by
    calc
      ∫ x, wc x ∂μ = inner ℝ oneLp wc := by
        change _ = inner ℝ
          (indicatorConstLp 2 MeasurableSet.univ
            (measure_ne_top μ Set.univ) (1 : ℝ)) wc
        simpa only [Measure.restrict_univ] using
          (MeasureTheory.L2.inner_indicatorConstLp_one MeasurableSet.univ
            (measure_ne_top μ Set.univ) wc).symm
      _ = inner ℝ oneLp v := by rw [← hwc]; exact hinner
      _ = ∫ x, v x ∂μ := by
        change inner ℝ
          (indicatorConstLp 2 MeasurableSet.univ
            (measure_ne_top μ Set.univ) (1 : ℝ)) v = _
        simpa only [Measure.restrict_univ] using
          (MeasureTheory.L2.inner_indicatorConstLp_one MeasurableSet.univ
            (measure_ne_top μ Set.univ) v)
  have hc : c = ∫ x, f x ∂μ := by
    calc
      c = ∫ x, wc x ∂μ := by
        rw [integral_congr_ae hwc_ae]
        simp
      _ = ∫ x, v x ∂μ := hinner'
      _ = ∫ x, f x ∂μ := integral_congr_ae hv_ae
  subst c
  simpa [U, v, wc, hwc] using hlim

/-- The representative of an iterated Koopman translate is almost
everywhere the corresponding pointwise translate. -/
theorem coe_koopmanL2_iterate_ae
    {X : Type*} [MeasurableSpace X]
    (T : X → X) (μ : Measure X) (hT : MeasurePreserving T μ μ)
    (v : Lp ℝ (2 : ℝ≥0∞) μ) (i : ℕ) :
    (((koopmanL2 T μ hT)^[i] v : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      fun x ↦ v (T^[i] x) := by
  have hfun : (koopmanL2 T μ hT : Lp ℝ 2 μ → Lp ℝ 2 μ) =
      Lp.compMeasurePreserving T hT := rfl
  rw [hfun, Lp.compMeasurePreserving_iterate hT i]
  exact Lp.coeFn_compMeasurePreserving v (hT.iterate i)

/-- The `L²` Birkhoff sum has the expected pointwise representative. -/
theorem coe_birkhoffSum_koopmanL2_ae
    {X : Type*} [MeasurableSpace X]
    (T : X → X) (μ : Measure X) (hT : MeasurePreserving T μ μ)
    (v : Lp ℝ (2 : ℝ≥0∞) μ) (n : ℕ) :
    ((birkhoffSum (koopmanL2 T μ hT) id n v : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      fun x ↦ birkhoffSum T (fun y ↦ v y) n x := by
  simp only [birkhoffSum]
  induction n with
  | zero =>
      filter_upwards [Lp.coeFn_zero ℝ (2 : ℝ≥0∞) μ] with x hx
      simpa only [Finset.sum_range_zero, Pi.zero_apply] using hx
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      have hadd :
          (((∑ k ∈ Finset.range n, (koopmanL2 T μ hT)^[k] v) +
              (koopmanL2 T μ hT)^[n] v : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
            fun x ↦
              ((∑ k ∈ Finset.range n, (koopmanL2 T μ hT)^[k] v :
                  Lp ℝ 2 μ) : X → ℝ) x +
                (((koopmanL2 T μ hT)^[n] v : Lp ℝ 2 μ) : X → ℝ) x :=
        Lp.coeFn_add _ _
      filter_upwards [hadd, ih, coe_koopmanL2_iterate_ae T μ hT v n] with x h₁ h₂ h₃
      change
        (((∑ k ∈ Finset.range n, (koopmanL2 T μ hT)^[k] v) +
            (koopmanL2 T μ hT)^[n] v : Lp ℝ 2 μ) : X → ℝ) x = _
      have h₂' :
          (((∑ k ∈ Finset.range n, (koopmanL2 T μ hT)^[k] v :
              Lp ℝ 2 μ) : X → ℝ) x) =
            ∑ k ∈ Finset.range n, v (T^[k] x) := by
        simpa only [id_eq] using h₂
      rw [h₁, h₂']
      simpa only [id_eq] using congrArg
        (fun y ↦ (∑ i ∈ Finset.range n, v (T^[i] x)) + y) h₃

/-- The `L²` Birkhoff average has the expected pointwise representative. -/
theorem coe_birkhoffAverage_koopmanL2_ae
    {X : Type*} [MeasurableSpace X]
    (T : X → X) (μ : Measure X) (hT : MeasurePreserving T μ μ)
    (v : Lp ℝ (2 : ℝ≥0∞) μ) (n : ℕ) :
    ((birkhoffAverage ℝ (koopmanL2 T μ hT) id n v : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      fun x ↦ birkhoffAverage ℝ T (fun y ↦ v y) n x := by
  simp only [birkhoffAverage]
  filter_upwards [Lp.coeFn_smul (n : ℝ)⁻¹
      (birkhoffSum (koopmanL2 T μ hT) id n v),
    coe_birkhoffSum_koopmanL2_ae T μ hT v n] with x h₁ h₂
  simpa only [Pi.smul_apply, smul_eq_mul] using
    h₁.trans (congrArg ((n : ℝ)⁻¹ * ·) h₂)

/-- For a bounded continuous observable, the `L²` average is represented
almost everywhere by its genuine pointwise orbit average. -/
theorem coe_birkhoffAverage_toLp_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (T : X → X) (μ : Measure X) (hT : MeasurePreserving T μ μ)
    [IsFiniteMeasure μ]
    (f : BoundedContinuousFunction X ℝ) (n : ℕ) :
    ((birkhoffAverage ℝ (koopmanL2 T μ hT) id n
        (BoundedContinuousFunction.toLp 2 μ ℝ f) : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ]
      fun x ↦ birkhoffAverage ℝ T f n x := by
  let v := BoundedContinuousFunction.toLp 2 μ ℝ f
  have hv : (v : X → ℝ) =ᵐ[μ] f := by
    simpa [v] using f.coeFn_toLp 2 μ ℝ
  have hall : ∀ᵐ x ∂μ, ∀ i : ℕ, v (T^[i] x) = f (T^[i] x) := by
    apply ae_all_iff.2
    intro i
    exact (hT.iterate i).quasiMeasurePreserving.ae hv
  have hsum :
      (fun x ↦ ∑ i ∈ Finset.range n, v (T^[i] x)) =ᵐ[μ]
        fun x ↦ ∑ i ∈ Finset.range n, f (T^[i] x) := by
    filter_upwards [hall] with x hx
    apply Finset.sum_congr rfl
    intro i _
    exact hx i
  have havg :
      (fun x ↦ birkhoffAverage ℝ T (fun y ↦ v y) n x) =ᵐ[μ]
        fun x ↦ birkhoffAverage ℝ T f n x := by
    filter_upwards [hsum] with x hx
    simpa only [birkhoffAverage, birkhoffSum, Pi.smul_apply, smul_eq_mul] using
      congrArg ((n : ℝ)⁻¹ * ·) hx
  exact (coe_birkhoffAverage_koopmanL2_ae T μ hT v n).trans havg

/-- Prefix orbit averages are contractions in the uniform norm on
observables. -/
theorem abs_birkhoffAverage_sub_le_norm
    {X : Type*} [TopologicalSpace X]
    (T : X → X) (f g : BoundedContinuousFunction X ℝ) (n : ℕ) (x : X) :
    |birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T g n x| ≤ ‖f - g‖ := by
  cases n with
  | zero => simp [birkhoffAverage, birkhoffSum]
  | succ n =>
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
      calc
        |((n + 1 : ℕ) : ℝ)⁻¹| *
              |∑ i ∈ Finset.range (n + 1), (f (T^[i] x) - g (T^[i] x))| ≤
            |((n + 1 : ℕ) : ℝ)⁻¹| *
              ∑ i ∈ Finset.range (n + 1), |f (T^[i] x) - g (T^[i] x)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
        _ ≤ |((n + 1 : ℕ) : ℝ)⁻¹| *
              ∑ _i ∈ Finset.range (n + 1), ‖f - g‖ := by
          gcongr with i hi
          simpa only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
            Real.norm_eq_abs] using (f - g).norm_coe_le_norm (T^[i] x)
        _ = ‖f - g‖ := by
          have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            Nat.cast_add, Nat.cast_one]
          rw [abs_of_pos (inv_pos.mpr hn)]
          field_simp

/-- Integration against a probability measure is a contraction for the
uniform norm. -/
theorem abs_integral_sub_le_norm
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : BoundedContinuousFunction X ℝ) :
    |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ ‖f - g‖ := by
  rw [← integral_sub (f.integrable μ) (g.integrable μ)]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x ↦ f x - g x) (C := ‖f - g‖)
      (Eventually.of_forall fun x ↦ by
        simpa only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
          Real.norm_eq_abs] using (f - g).norm_coe_le_norm x))

/-! The next diagonal lemma turns countably many convergences in measure
into almost-everywhere convergence along one common subsequence.  It is
stated abstractly because the same selection is used for all members of a
countable dense family of continuous observables. -/

/-- A strictly increasing sequence of natural-number indices. -/
structure Subseq where
  seq : ℕ → ℕ
  mono : StrictMono seq

namespace Subseq

instance : CoeFun Subseq (fun _ ↦ ℕ → ℕ) := ⟨seq⟩

def id : Subseq := ⟨fun n ↦ n, strictMono_id⟩

def comp (s r : Subseq) : Subseq :=
  ⟨s ∘ r, s.mono.comp r.mono⟩

end Subseq

noncomputable def extractedSubseq {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} {f : ℕ → X → E} {g : X → E}
    (h : TendstoInMeasure μ f atTop g) : Subseq :=
  ⟨Classical.choose h.exists_seq_tendsto_ae,
    (Classical.choose_spec h.exists_seq_tendsto_ae).1⟩

theorem extractedSubseq_ae {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} {f : ℕ → X → E} {g : X → E}
    (h : TendstoInMeasure μ f atTop g) :
    ∀ᵐ x ∂μ, Tendsto (fun i ↦ f (extractedSubseq h i) x) atTop (𝓝 (g x)) :=
  (Classical.choose_spec h.exists_seq_tendsto_ae).2

noncomputable def subseqTower {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) : ℕ → Subseq
  | 0 => extractedSubseq (h 0)
  | j + 1 =>
      let s := subseqTower f g h j
      s.comp (extractedSubseq ((h (j + 1)).comp s.mono.tendsto_atTop))

theorem subseqTower_ae {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) (j : ℕ) :
    ∀ᵐ x ∂μ, Tendsto (fun i ↦ f j (subseqTower f g h j i) x) atTop (𝓝 (g j x)) := by
  cases j with
  | zero => exact extractedSubseq_ae (h 0)
  | succ j =>
      exact extractedSubseq_ae ((h (j + 1)).comp
        (subseqTower f g h j).mono.tendsto_atTop)

noncomputable def towerStep {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) (j : ℕ) : Subseq :=
  extractedSubseq ((h (j + 1)).comp (subseqTower f g h j).mono.tendsto_atTop)

theorem subseqTower_succ {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) (j : ℕ) :
    subseqTower f g h (j + 1) = (subseqTower f g h j).comp (towerStep f g h j) := rfl

noncomputable def towerFactor {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) (j : ℕ) : ℕ → Subseq
  | 0 => Subseq.id
  | d + 1 => (towerFactor f g h j d).comp (towerStep f g h (j + d))

theorem subseqTower_add {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) (j d : ℕ) :
    subseqTower f g h (j + d) =
      (subseqTower f g h j).comp (towerFactor f g h j d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Nat.add_succ, subseqTower_succ, ih]
      rfl

noncomputable def diagonalSubseq {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) : ℕ → ℕ :=
  fun n ↦ subseqTower f g h n n

/-- Countably many convergences in measure have one common subsequence on
which they all converge almost everywhere. -/
theorem exists_diagonal_tendsto_ae {X E : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace E] {μ : Measure X} (f : ℕ → ℕ → X → E) (g : ℕ → X → E)
    (h : ∀ j, TendstoInMeasure μ (f j) atTop (g j)) :
    ∃ ns : ℕ → ℕ, Tendsto ns atTop atTop ∧
      ∀ᵐ x ∂μ, ∀ j, Tendsto (fun n ↦ f j (ns n) x) atTop (𝓝 (g j x)) := by
  let ns := diagonalSubseq f g h
  refine ⟨ns, ?_, ?_⟩
  · exact tendsto_atTop_mono
      (fun n ↦ (subseqTower f g h n).mono.id_le n) tendsto_id
  · apply ae_all_iff.2
    intro j
    filter_upwards [subseqTower_ae f g h j] with x hx
    apply (tendsto_add_atTop_iff_nat j).mp
    have hq : Tendsto
        (fun d ↦ towerFactor f g h j d (j + d)) atTop atTop := by
      exact tendsto_atTop_mono
        (fun d ↦ le_trans (Nat.le_add_left d j)
          ((towerFactor f g h j d).mono.id_le (j + d))) tendsto_id
    have hcomp := hx.comp hq
    convert hcomp using 1
    funext d
    dsimp [ns, diagonalSubseq]
    rw [Nat.add_comm d j]
    rw [subseqTower_add]
    rfl

/-- A dense test family has one common pointwise generic subsequence. -/
theorem exists_dense_pointwise_generic_subsequence
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) :
    ∃ G : ℕ → BoundedContinuousFunction X ℝ, DenseRange G ∧
      ∃ x : X, x ∈ μ.support ∧ ∃ ns : ℕ → ℕ, Tendsto ns atTop atTop ∧
        ∀ j, Tendsto
          (fun n ↦ birkhoffAverage ℝ T (G j) (ns n) x) atTop
          (nhds (∫ y, G j y ∂μ)) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : TopologicalSpace.SeparableSpace
      (BoundedContinuousFunction X ℝ) := by
    let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
    exact e.surjective.denseRange.separableSpace e.continuous
  obtain ⟨G, hG⟩ := TopologicalSpace.exists_dense_seq
      (BoundedContinuousFunction X ℝ)
  let F : ℕ → ℕ → X → ℝ :=
    fun j n x ↦ birkhoffAverage ℝ T (G j) n x
  let c : ℕ → X → ℝ := fun j _ ↦ ∫ y, G j y ∂μ
  have hmeasure : ∀ j, TendstoInMeasure μ (F j) atTop (c j) := by
    intro j
    have hlp := meanErgodic_limit_ae_const T μ hT (G j)
    have hm := tendstoInMeasure_of_tendsto_Lp hlp
    have hm' : TendstoInMeasure μ (F j) atTop
        (indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top μ Set.univ) (∫ y, G j y ∂μ) : X → ℝ) :=
      TendstoInMeasure.congr_left
        (fun n ↦ coe_birkhoffAverage_toLp_ae T μ hT.1 (G j) n) hm
    have hc :
        ((indicatorConstLp 2 MeasurableSet.univ
          (measure_ne_top μ Set.univ) (∫ y, G j y ∂μ) :
            Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] c j := by
      simpa [c] using
        (@indicatorConstLp_coeFn X ℝ _ 2 μ _ Set.univ
          MeasurableSet.univ (measure_ne_top μ Set.univ)
          (∫ y, G j y ∂μ))
    exact TendstoInMeasure.congr_right hc hm'
  obtain ⟨ns, hns, hpoint⟩ := exists_diagonal_tendsto_ae F c hmeasure
  obtain ⟨x, hx, hxsupport⟩ := (hpoint.and Measure.support_mem_ae).exists
  exact ⟨G, hG, x, hxsupport, ns, hns, fun j ↦ hx j⟩

/-- Every ergodic probability measure on a compact metrizable system has
a point that is weakly generic along a subsequence of prefix lengths. -/
theorem exists_pointwise_generic_subsequence
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) :
    ∃ x : X, x ∈ μ.support ∧ ∃ ns : ℕ → ℕ, Tendsto ns atTop atTop ∧
      ∀ f : BoundedContinuousFunction X ℝ,
        Tendsto (fun n ↦ birkhoffAverage ℝ T f (ns n) x) atTop
          (nhds (∫ y, f y ∂μ)) := by
  obtain ⟨G, hG, x, hxsupport, ns, hns, hGconv⟩ :=
    exists_dense_pointwise_generic_subsequence T μ hT
  refine ⟨x, hxsupport, ns, hns, ?_⟩
  intro f
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨j, hj⟩ := hG.exists_dist_lt f (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hGconv j) (ε / 3) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have havg : dist (birkhoffAverage ℝ T f (ns n) x)
        (birkhoffAverage ℝ T (G j) (ns n) x) ≤ ‖f - G j‖ := by
    simpa only [Real.dist_eq] using
      abs_birkhoffAverage_sub_le_norm T f (G j) (ns n) x
  have hint : dist (∫ y, G j y ∂μ) (∫ y, f y ∂μ) ≤ ‖f - G j‖ := by
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_sub_le_norm μ f (G j)
  have hnorm : ‖f - G j‖ < ε / 3 := by
    simpa only [dist_eq_norm] using hj
  calc
    dist (birkhoffAverage ℝ T f (ns n) x) (∫ y, f y ∂μ) ≤
        dist (birkhoffAverage ℝ T f (ns n) x)
            (birkhoffAverage ℝ T (G j) (ns n) x) +
          dist (birkhoffAverage ℝ T (G j) (ns n) x) (∫ y, G j y ∂μ) +
          dist (∫ y, G j y ∂μ) (∫ y, f y ∂μ) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      exact add_lt_add (add_lt_add (havg.trans_lt hnorm) (hN n hn))
        (hint.trans_lt hnorm)
    _ = ε := by ring

/-- The coding point is generic for `μ` along intervals with the indicated
starting positions and lengths. -/
def IsGenericAlongOrbitIntervals {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (T : X → X) (a : X) (μ : Measure X)
    (start length : ℕ → ℕ) : Prop :=
  Tendsto length atTop atTop ∧
    ∀ f : BoundedContinuousFunction X ℝ,
      Tendsto
        (fun k ↦ birkhoffAverage ℝ T f (length k) (T^[start k] a))
        atTop (nhds (∫ x, f x ∂μ))

theorem continuous_birkhoffAverage_of_continuous {X : Type*}
    [TopologicalSpace X] (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (hf : Continuous f) (n : ℕ) :
    Continuous (fun x => birkhoffAverage ℝ T f n x) := by
  unfold birkhoffAverage birkhoffSum
  fun_prop

/-- If an ergodic measure is carried by the forward orbit closure of the
coding point, then that coding point is generic for the measure along a
sequence of long intervals.  This is the pointed correspondence principle
needed by the KMRR dynamical theorem. -/
theorem exists_genericAlongOrbitIntervals_of_carried
    (A : Set ℕ) (ν : ProbabilityMeasure SymbolicSpace)
    (hνerg : Ergodic symbolicShift (ν : Measure SymbolicSpace))
    (hνcarried : ν ∈ carriedProbabilities A) :
    ∃ start length : ℕ → ℕ,
      IsGenericAlongOrbitIntervals symbolicShift (symbolicPoint A)
        (ν : Measure SymbolicSpace) start length := by
  obtain ⟨G, hG, y, hysupport, ns, hns, hGconv⟩ :=
    exists_dense_pointwise_generic_subsequence symbolicShift
      (ν : Measure SymbolicSpace) hνerg
  have hyclosure : y ∈ orbitClosure A :=
    support_subset_orbitClosure_of_mem_carried hνcarried hysupport
  let W : ℕ → Set SymbolicSpace := fun k =>
    ⋂ j ∈ Finset.range (k + 1),
      {x | dist
        (birkhoffAverage ℝ symbolicShift (G j) (ns k) x)
        (birkhoffAverage ℝ symbolicShift (G j) (ns k) y) <
          (1 : ℝ) / (k + 1)}
  have hWopen (k : ℕ) : IsOpen (W k) := by
    dsimp [W]
    apply isOpen_biInter_finset
    intro j hj
    apply isOpen_lt
    · exact (continuous_birkhoffAverage_of_continuous symbolicShift
        continuous_symbolicShift (G j) (G j).continuous (ns k)).dist
          continuous_const
    · fun_prop
  have hyW (k : ℕ) : y ∈ W k := by
    simp only [W, Set.mem_iInter, Set.mem_ofPred_eq]
    intro j
    simp only [Finset.mem_range]
    intro hj
    simp only [dist_self]
    positivity
  have hexists (k : ℕ) :
      ∃ m : ℕ, symbolicShift^[m] (symbolicPoint A) ∈ W k := by
    obtain ⟨z, hzW, hzrange⟩ :=
      (mem_closure_iff.mp hyclosure) (W k) (hWopen k) (hyW k)
    obtain ⟨m, rfl⟩ := hzrange
    exact ⟨m, hzW⟩
  let start : ℕ → ℕ := fun k => (hexists k).choose
  have hstart (k : ℕ) :
      symbolicShift^[start k] (symbolicPoint A) ∈ W k :=
    (hexists k).choose_spec
  have hGtransfer (j : ℕ) :
      Tendsto
        (fun k ↦ birkhoffAverage ℝ symbolicShift (G j) (ns k)
          (symbolicShift^[start k] (symbolicPoint A)))
        atTop (nhds (∫ x, G j x ∂(ν : Measure SymbolicSpace))) := by
    have herr : Tendsto
        (fun k ↦ dist
          (birkhoffAverage ℝ symbolicShift (G j) (ns k)
            (symbolicShift^[start k] (symbolicPoint A)))
          (birkhoffAverage ℝ symbolicShift (G j) (ns k) y))
        atTop (nhds 0) := by
      have hmajor : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1))
          atTop (nhds 0) := by
        have hsucc : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
          tendsto_atTop_mono' atTop
            (Eventually.of_forall fun k : ℕ => Nat.le_succ k) tendsto_id
        have hcast : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ))
            atTop atTop := tendsto_natCast_atTop_atTop.comp hsucc
        have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero
        simpa [one_div, Function.comp_def, Nat.cast_add, Nat.cast_one] using
          hinv.comp hcast
      refine squeeze_zero' (Eventually.of_forall fun k => dist_nonneg)
        ?_ hmajor
      filter_upwards [eventually_ge_atTop j] with k hk
      have hkW := hstart k
      simp only [W, Set.mem_iInter, Set.mem_ofPred_eq] at hkW
      exact (hkW j (by simpa using Nat.lt_succ_of_le hk)).le
    exact (hGconv j).congr_uniformity
      (tendsto_uniformity_iff_dist_tendsto_zero.mpr
        (by simpa only [dist_comm] using herr))
  refine ⟨start, ns, hns, ?_⟩
  intro f
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨j, hj⟩ := hG.exists_dist_lt f (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hGtransfer j)
    (ε / 3) (by positivity)
  refine ⟨N, fun k hk ↦ ?_⟩
  have havg : dist
        (birkhoffAverage ℝ symbolicShift f (ns k)
          (symbolicShift^[start k] (symbolicPoint A)))
        (birkhoffAverage ℝ symbolicShift (G j) (ns k)
          (symbolicShift^[start k] (symbolicPoint A))) ≤ ‖f - G j‖ := by
    simpa only [Real.dist_eq] using
      abs_birkhoffAverage_sub_le_norm symbolicShift f (G j) (ns k)
        (symbolicShift^[start k] (symbolicPoint A))
  have hint : dist (∫ x, G j x ∂(ν : Measure SymbolicSpace))
        (∫ x, f x ∂(ν : Measure SymbolicSpace)) ≤ ‖f - G j‖ := by
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_sub_le_norm (ν : Measure SymbolicSpace) f (G j)
  have hnorm : ‖f - G j‖ < ε / 3 := by
    simpa only [dist_eq_norm] using hj
  calc
    dist
        (birkhoffAverage ℝ symbolicShift f (ns k)
          (symbolicShift^[start k] (symbolicPoint A)))
        (∫ x, f x ∂(ν : Measure SymbolicSpace)) ≤
      dist
          (birkhoffAverage ℝ symbolicShift f (ns k)
            (symbolicShift^[start k] (symbolicPoint A)))
          (birkhoffAverage ℝ symbolicShift (G j) (ns k)
            (symbolicShift^[start k] (symbolicPoint A))) +
        dist
          (birkhoffAverage ℝ symbolicShift (G j) (ns k)
            (symbolicShift^[start k] (symbolicPoint A)))
          (∫ x, G j x ∂(ν : Measure SymbolicSpace)) +
        dist (∫ x, G j x ∂(ν : Measure SymbolicSpace))
          (∫ x, f x ∂(ν : Measure SymbolicSpace)) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      exact add_lt_add (add_lt_add (havg.trans_lt hnorm) (hN k hk))
        (hint.trans_lt hnorm)
    _ = ε := by ring

/-- The pointed correspondence construction up to the final orbit-block
transfer: the ergodic measure has positive cylinder mass and admits a generic
point lying in the forward orbit closure of the original coding point. -/
theorem exists_carried_generic_point {A : Set ℕ}
    (hA : HasPositiveUpperDensity A) :
    ∃ ν : ProbabilityMeasure SymbolicSpace,
      Ergodic symbolicShift (ν : Measure SymbolicSpace) ∧
        0 < (ν : Measure SymbolicSpace) originCylinder ∧
          ∃ y ∈ orbitClosure A, ∃ ns : ℕ → ℕ,
            Tendsto ns atTop atTop ∧
              ∀ f : BoundedContinuousFunction SymbolicSpace ℝ,
                Tendsto
                  (fun n ↦ birkhoffAverage ℝ symbolicShift f (ns n) y)
                  atTop (nhds (∫ z, f z ∂(ν : Measure SymbolicSpace))) := by
  obtain ⟨ν, hνerg, hνcarried, hνorigin⟩ :=
    exists_carried_ergodic_probability hA
  obtain ⟨y, hysupport, ns, hns, hygen⟩ :=
    exists_pointwise_generic_subsequence symbolicShift
      (ν : Measure SymbolicSpace) hνerg
  refine ⟨ν, hνerg, hνorigin, y,
    support_subset_orbitClosure_of_mem_carried hνcarried hysupport,
    ns, hns, hygen⟩

/-- Pointed Furstenberg correspondence for the exact coding point: positive
upper density gives an ergodic measure of positive cylinder mass for which
the original coding point is generic along long intervals. -/
theorem exists_pointed_ergodic_intervalGeneric {A : Set ℕ}
    (hA : HasPositiveUpperDensity A) :
    ∃ ν : ProbabilityMeasure SymbolicSpace, ∃ start length : ℕ → ℕ,
      Ergodic symbolicShift (ν : Measure SymbolicSpace) ∧
        0 < (ν : Measure SymbolicSpace) originCylinder ∧
          IsGenericAlongOrbitIntervals symbolicShift (symbolicPoint A)
            (ν : Measure SymbolicSpace) start length := by
  obtain ⟨ν, hνerg, hνcarried, hνorigin⟩ :=
    exists_carried_ergodic_probability hA
  obtain ⟨start, length, hgeneric⟩ :=
    exists_genericAlongOrbitIntervals_of_carried A ν hνerg hνcarried
  exact ⟨ν, start, length, hνerg, hνorigin, hgeneric⟩

/-- A three-term Erdős progression: one sequence of times sends
`(x₀, x₁)` to `(x₁, x₂)`. -/
def IsErdosProgression {X : Type*} [TopologicalSpace X] (T : X → X)
    (x₀ x₁ x₂ : X) : Prop :=
  ∃ c : ℕ → ℕ, StrictMono c ∧
    Tendsto (fun n => (T^[c n] x₀, T^[c n] x₁)) atTop (𝓝 (x₁, x₂))

/-- In a first-countable space, a product-orbit cluster point is represented
by a strictly increasing sequence and hence is an Erdős progression. -/
theorem isErdosProgression_of_mapClusterPt {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology (X × X)] (T : X → X) (x₀ x₁ x₂ : X)
    (hcluster : MapClusterPt (x₁, x₂) atTop
      (fun n : ℕ => (T^[n] x₀, T^[n] x₁))) :
    IsErdosProgression T x₀ x₁ x₂ := by
  obtain ⟨c, hc, hlim⟩ := hcluster.tendsto_subseq
  refine ⟨c, hc, ?_⟩
  simpa [Function.comp_def] using hlim

/-- The exact topological consequence of measure-genericity used at the end
of the KMRR argument: every support point is a cluster point of the orbit. -/
def IsSupportGeneric {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (u : ℕ → X) (μ : MeasureTheory.Measure X) : Prop :=
  ∀ y ∈ μ.support, MapClusterPt y atTop u

/-- A support-generic product orbit yields an Erdős progression to every
point in the support of its limiting measure. -/
theorem isErdosProgression_of_supportGeneric {X : Type*}
    [MeasurableSpace (X × X)] [TopologicalSpace X]
    [FirstCountableTopology (X × X)] (T : X → X) (x₀ x₁ x₂ : X)
    (μ : MeasureTheory.Measure (X × X))
    (hgeneric : IsSupportGeneric
      (fun n : ℕ => (T^[n] x₀, T^[n] x₁)) μ)
    (hsupport : (x₁, x₂) ∈ μ.support) :
    IsErdosProgression T x₀ x₁ x₂ :=
  isErdosProgression_of_mapClusterPt T x₀ x₁ x₂
    (hgeneric (x₁, x₂) hsupport)

/-! ### Generic orbit blocks and support -/

/-- Weak genericity of a sequence along finite averaging blocks.  This is
the test-function formulation used in the generic-pair transfer lemma of
Kra--Moreira--Richter--Robertson. -/
def IsWeaklyGenericAlong {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (u : ℕ → X) (μ : Measure X)
    (Φ : ℕ → Finset ℕ) : Prop :=
  ∀ f : BoundedContinuousFunction X ℝ,
    Tendsto (fun k ↦ ((Φ k).card : ℝ)⁻¹ * ∑ n ∈ Φ k, f (u n)) atTop
      (𝓝 (∫ x, f x ∂μ))

/-- The shifted interval of orbit times associated to one of the pointed
averages furnished by the correspondence principle. -/
def orbitIntervalBlocks (start length : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (length k)).image fun r => start k + r

theorem card_orbitIntervalBlocks (start length : ℕ → ℕ) (k : ℕ) :
    (orbitIntervalBlocks start length k).card = length k := by
  rw [orbitIntervalBlocks, Finset.card_image_iff.mpr]
  · exact Finset.card_range _
  · intro i hi j hj hij
    exact Nat.add_left_cancel hij

theorem sum_orbitIntervalBlocks {X E : Type*} [AddCommMonoid E]
    (T : X → X) (a : X) (start length : ℕ → ℕ) (k : ℕ)
    (f : X → E) :
    ∑ n ∈ orbitIntervalBlocks start length k, f (T^[n] a) =
      ∑ r ∈ Finset.range (length k), f (T^[r] (T^[start k] a)) := by
  rw [orbitIntervalBlocks, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r hr
    simp only [← Function.iterate_add_apply, Nat.add_comm]
  · intro i hi j hj hij
    exact Nat.add_left_cancel hij

/-- Pointed genericity along shifted intervals is precisely weak genericity
of the original orbit along the corresponding finite blocks. -/
theorem weaklyGenericAlong_orbitIntervalBlocks
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (T : X → X) (a : X) (μ : Measure X)
    (start length : ℕ → ℕ)
    (hgeneric : IsGenericAlongOrbitIntervals T a μ start length) :
    IsWeaklyGenericAlong (fun n => T^[n] a) μ
      (orbitIntervalBlocks start length) := by
  intro f
  have h := hgeneric.2 f
  simpa only [birkhoffAverage, birkhoffSum,
    card_orbitIntervalBlocks, sum_orbitIntervalBlocks,
    smul_eq_mul] using h

/-- A weak limit of the concrete empirical measures is exactly a genericity
statement for the corresponding prefix blocks. -/
theorem weaklyGenericAlong_of_empirical_tendsto (A : Set ℕ)
    (μ : ProbabilityMeasure SymbolicSpace) (N : ℕ → ℕ)
    (hlim : Tendsto (fun k => empiricalMeasure A (N k - 1)) atTop (𝓝 μ)) :
    IsWeaklyGenericAlong
      (fun n => symbolicShift^[n] (symbolicPoint A)) μ
      (fun k => Finset.range (N k - 1 + 1)) := by
  intro f
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  simpa only [integral_empiricalMeasure, Finset.card_range] using h

/-- Every time appearing in the averaging blocks eventually lies beyond any
fixed cutoff. -/
def OrbitBlocksEscape (Φ : ℕ → Finset ℕ) : Prop :=
  ∀ M : ℕ, ∀ᶠ k in atTop, ∀ n ∈ Φ k, M < n

/-- The union of all forward return targets of a set. -/
def forwardSaturation {X : Type*} (T : X → X) (E : Set X) : Set X :=
  ⋃ n : ℕ, (T^[n]) ⁻¹' E

/-- In an ergodic finite system, the forward saturation of every positive
measurable set is conull. -/
theorem ae_mem_forwardSaturation_of_ergodic
    {X : Type*} [MeasurableSpace X] {T : X → X} {μ : Measure X}
    [IsFiniteMeasure μ] (hT : Ergodic T μ) {E : Set X}
    (hE : MeasurableSet E) (hEpos : μ E ≠ 0) :
    ∀ᵐ x ∂μ, x ∈ forwardSaturation T E := by
  let S : Set X := forwardSaturation T E
  have hSm : MeasurableSet S := by
    exact MeasurableSet.iUnion fun n => hE.preimage (hT.measurable.iterate n)
  have hpre : T ⁻¹' S ⊆ S := by
    rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    simpa only [Set.mem_preimage, Function.iterate_succ_apply] using hn
  rcases hT.ae_empty_or_univ_of_preimage_ae_le hSm.nullMeasurableSet
      (Eventually.of_forall hpre) with hzero | hfull
  · exfalso
    apply hEpos
    apply measure_mono_null (show E ⊆ S by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩)
    simpa using measure_congr hzero
  · filter_upwards [hfull] with x hx
    change x ∈ S
    exact hx.mpr (Set.mem_univ x)

/-- A weakly generic orbit sampled on blocks escaping to infinity visits
every neighborhood of every support point arbitrarily late. -/
theorem supportGeneric_of_weaklyGenericAlong
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] [NormalSpace X] [T1Space X] [BorelSpace X]
    (u : ℕ → X) (μ : Measure X) [IsFiniteMeasure μ]
    (Φ : ℕ → Finset ℕ)
    (hgeneric : IsWeaklyGenericAlong u μ Φ)
    (hescape : OrbitBlocksEscape Φ) :
    IsSupportGeneric u μ := by
  rw [IsSupportGeneric]
  intro y hy
  rw [mapClusterPt_iff_frequently]
  intro U hU
  rw [frequently_atTop]
  intro M
  obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
  obtain ⟨f, hfzero, hfone, hfIcc⟩ :=
    exists_continuous_zero_one_of_isClosed
      hVopen.isClosed_compl isClosed_singleton
      (Set.disjoint_left.2 (by
        intro z hzU hzY
        exact hzU (hzY ▸ hyV)))
  let fb : BoundedContinuousFunction X ℝ :=
    BoundedContinuousFunction.mkOfCompact f
  have hfy : fb y = 1 := by
    simpa [fb] using hfone (Set.mem_singleton y)
  have hnonneg : 0 ≤ (fb : X → ℝ) := fun z ↦ by
    simpa [fb] using (hfIcc z).1
  have hsupportPos : 0 < μ {z | fb z ≠ 0} := by
    apply (Measure.mem_support_iff_forall y).mp hy
    apply IsOpen.mem_nhds
    · exact isOpen_ne_fun fb.continuous continuous_const
    · simp [hfy]
  have hintPos : 0 < ∫ z, fb z ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnonneg (fb.integrable μ)]
    simpa only [Function.support] using hsupportPos
  have havg : ∀ᶠ k in atTop,
      0 < ((Φ k).card : ℝ)⁻¹ * ∑ n ∈ Φ k, fb (u n) :=
    (hgeneric fb).eventually (isOpen_Ioi.mem_nhds hintPos)
  obtain ⟨k, hkavg, hkescape⟩ := (havg.and (hescape M)).exists
  have hsum : 0 < ∑ n ∈ Φ k, fb (u n) := by
    by_contra h
    have hsumle : ∑ n ∈ Φ k, fb (u n) ≤ 0 := le_of_not_gt h
    have hinvnonneg : 0 ≤ ((Φ k).card : ℝ)⁻¹ :=
      inv_nonneg.2 (Nat.cast_nonneg _)
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hinvnonneg hsumle)) hkavg
  have hterms : ∀ n ∈ Φ k, 0 ≤ fb (u n) := fun n _ ↦ hnonneg (u n)
  obtain ⟨n, hnΦ, hnpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hterms).mp hsum
  refine ⟨n, (hkescape n hnΦ).le, ?_⟩
  apply hVU
  by_contra hnv
  have hncomp : u n ∈ Vᶜ := by simpa using hnv
  have hzero := hfzero hncomp
  exact hnpos.ne' (by simpa [fb] using hzero)

/-- A version of `supportGeneric_of_weaklyGenericAlong` adapted to Følner
blocks: it is enough that their cardinalities tend to infinity.  A bounded
number of early orbit terms then has asymptotically zero weight, so positive
mass in every neighborhood of a support point forces arbitrarily late
visits. -/
theorem supportGeneric_of_weaklyGenericAlong_card_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] [NormalSpace X] [T1Space X] [BorelSpace X]
    (u : ℕ → X) (μ : Measure X) [IsFiniteMeasure μ]
    (Φ : ℕ → Finset ℕ)
    (hgeneric : IsWeaklyGenericAlong u μ Φ)
    (hcard : Tendsto (fun k => (Φ k).card) atTop atTop) :
    IsSupportGeneric u μ := by
  rw [IsSupportGeneric]
  intro y hy
  rw [mapClusterPt_iff_frequently]
  intro U hU
  rw [frequently_atTop]
  intro M
  obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
  obtain ⟨f, hfzero, hfone, hfIcc⟩ :=
    exists_continuous_zero_one_of_isClosed
      hVopen.isClosed_compl isClosed_singleton
      (Set.disjoint_left.2 (by
        intro z hzU hzY
        exact hzU (hzY ▸ hyV)))
  let fb : BoundedContinuousFunction X ℝ :=
    BoundedContinuousFunction.mkOfCompact f
  have hfy : fb y = 1 := by
    simpa [fb] using hfone (Set.mem_singleton y)
  have hnonneg : 0 ≤ (fb : X → ℝ) := fun z ↦ by
    simpa [fb] using (hfIcc z).1
  have hleone : ∀ z, fb z ≤ 1 := fun z ↦ by
    simpa [fb] using (hfIcc z).2
  have hsupportPos : 0 < μ {z | fb z ≠ 0} := by
    apply (Measure.mem_support_iff_forall y).mp hy
    apply IsOpen.mem_nhds
    · exact isOpen_ne_fun fb.continuous continuous_const
    · simp [hfy]
  have hintPos : 0 < ∫ z, fb z ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnonneg (fb.integrable μ)]
    simpa only [Function.support] using hsupportPos
  have havg : ∀ᶠ k in atTop,
      (∫ z, fb z ∂μ) / 2 <
        ((Φ k).card : ℝ)⁻¹ * ∑ n ∈ Φ k, fb (u n) :=
    (hgeneric fb).eventually
      (isOpen_Ioi.mem_nhds (half_lt_self hintPos))
  have hsmall : ∀ᶠ k in atTop,
      ((Φ k).card : ℝ)⁻¹ * M < (∫ z, fb z ∂μ) / 2 := by
    have hinv : Tendsto (fun k => (((Φ k).card : ℝ))⁻¹)
        atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp hcard)
    have hzero : Tendsto (fun k => (((Φ k).card : ℝ))⁻¹ * M)
        atTop (nhds 0) := by
      simpa using hinv.mul_const (M : ℝ)
    exact hzero.eventually (isOpen_Iio.mem_nhds (half_pos hintPos))
  obtain ⟨k, hkavg, hksmall⟩ := (havg.and hsmall).exists
  by_contra hno
  have hnolate : ∀ n ∈ Φ k, M ≤ n → fb (u n) = 0 := by
    intro n hn hnM
    have hnotV : u n ∉ V := by
      intro hnV
      apply hno
      exact ⟨n, hnM, hVU hnV⟩
    have hz := hfzero (by simpa using hnotV)
    simpa [fb] using hz
  have hsumle : ∑ n ∈ Φ k, fb (u n) ≤ M := by
    calc
      ∑ n ∈ Φ k, fb (u n) ≤
          ∑ n ∈ Φ k, if n < M then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hnM : n < M
        · simpa [hnM] using hleone (u n)
        · simp only [hnM, ↓reduceIte]
          rw [hnolate n hn (Nat.le_of_not_gt hnM)]
      _ = ((Φ k).filter fun n => n < M).card := by
        simp
      _ ≤ M := by
        have hcardle := Finset.card_le_card
          (show (Φ k).filter (fun n => n < M) ⊆ Finset.range M by
            intro n hn
            simpa using (Finset.mem_filter.mp hn).2)
        simpa using hcardle
  have havgle :
      ((Φ k).card : ℝ)⁻¹ * ∑ n ∈ Φ k, fb (u n) ≤
        ((Φ k).card : ℝ)⁻¹ * M :=
    mul_le_mul_of_nonneg_left hsumle
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact (not_lt_of_ge havgle) (hksmall.trans hkavg)

/-- In particular, a point generic along growing shifted intervals has every
point of the limiting measure's support as a forward orbit cluster point. -/
theorem supportGeneric_of_genericAlongOrbitIntervals
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] [NormalSpace X] [T1Space X] [BorelSpace X]
    (T : X → X) (a : X) (μ : Measure X) [IsFiniteMeasure μ]
    (start length : ℕ → ℕ)
    (hgeneric : IsGenericAlongOrbitIntervals T a μ start length) :
    IsSupportGeneric (fun n => T^[n] a) μ := by
  apply supportGeneric_of_weaklyGenericAlong_card_tendsto
    (fun n => T^[n] a) μ (orbitIntervalBlocks start length)
    (weaklyGenericAlong_orbitIntervalBlocks T a μ start length hgeneric)
  simpa only [card_orbitIntervalBlocks] using hgeneric.1

/-- The cylinder which tests the coordinate `t`.  It is written as a
preimage so that it works uniformly with the return-time notation. -/
def shiftedOriginCylinder (t : ℕ) : Set SymbolicSpace :=
  (symbolicShift^[t]) ⁻¹' originCylinder

theorem isOpen_shiftedOriginCylinder (t : ℕ) :
    IsOpen (shiftedOriginCylinder t) :=
  isClopen_originCylinder.isOpen.preimage (continuous_symbolicShift.iterate t)

/-- Returning to the coordinate-`t` cylinder at time `n` says exactly that
`n + t` belongs to the coded set. -/
theorem returnTimes_shiftedOriginCylinder (A : Set ℕ) (t : ℕ) :
    returnTimes symbolicShift (symbolicPoint A) (shiftedOriginCylinder t) =
      {n : ℕ | n + t ∈ A} := by
  ext n
  change symbolicShift^[t] (symbolicShift^[n] (symbolicPoint A)) 0 = true ↔ n + t ∈ A
  rw [symbolicShift_iterate_apply, symbolicShift_iterate_apply, zero_add]
  rw [show (t : ℤ) + n = ((t + n : ℕ) : ℤ) by norm_cast]
  simp only [symbolicPoint, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast,
    decide_eq_true_eq, Nat.add_comm]

/-- The precise pointed dynamical configuration needed for Problem 656. -/
def HasPointedKMRRProgression (A : Set ℕ) : Prop :=
  ∃ t : ℕ, ∃ x₁ x₂ : SymbolicSpace,
    x₁ ∈ originCylinder ∧ x₂ ∈ shiftedOriginCylinder t ∧
      IsErdosProgression symbolicShift (symbolicPoint A) x₁ x₂

/-! ### The progression-measure selection interface -/

/-- The precise measure package produced by the analytic KMRR argument. -/
def IsPointedProgressionMeasure (A : Set ℕ)
    (σ : MeasureTheory.Measure (SymbolicSpace × SymbolicSpace)) : Prop :=
  0 < σ (originCylinder ×ˢ (Set.univ : Set SymbolicSpace)) ∧
    ∀ᵐ p ∂σ,
      IsErdosProgression symbolicShift (symbolicPoint A) p.1 p.2 ∧
        p.2 ∈ ⋃ t : ℕ, shiftedOriginCylinder t

/-- The joining data isolated by the analytic part of the KMRR proof.
The first marginal is the invariant measure, the second marginal is
absolutely continuous with respect to it, and almost every sampled pair is
both generic for and in the support of its component measure. -/
def IsKMRRJoining (A : Set ℕ) (μ : Measure SymbolicSpace)
    (σ : Measure (SymbolicSpace × SymbolicSpace))
    (component : SymbolicSpace × SymbolicSpace →
      Measure (SymbolicSpace × SymbolicSpace)) : Prop :=
  Measure.map Prod.fst σ = μ ∧
    Measure.map Prod.snd σ ≪ μ ∧
      ∀ᵐ p ∂σ,
        IsSupportGeneric
          (fun n : ℕ =>
            (symbolicShift^[n] (symbolicPoint A),
              symbolicShift^[n] p.1)) (component p) ∧
          p ∈ (component p).support

/-- The joining identities, support property, and generic-pair property
produce the progression measure used by the elementary extraction. -/
theorem progressionMeasure_of_kmrrJoining {A : Set ℕ}
    {μ : Measure SymbolicSpace}
    {σ : Measure (SymbolicSpace × SymbolicSpace)}
    {component : SymbolicSpace × SymbolicSpace →
      Measure (SymbolicSpace × SymbolicSpace)}
    (hjoin : IsKMRRJoining A μ σ component)
    (hμorigin : 0 < μ originCylinder)
    (hsaturation : ∀ᵐ x ∂μ,
      x ∈ ⋃ t : ℕ, shiftedOriginCylinder t) :
    IsPointedProgressionMeasure A σ := by
  have hpre : Prod.fst ⁻¹' originCylinder =
      originCylinder ×ˢ (Set.univ : Set SymbolicSpace) := by
    ext p
    simp
  constructor
  · rw [← hpre, ← Measure.map_apply measurable_fst
      isClopen_originCylinder.isOpen.measurableSet, hjoin.1]
    exact hμorigin
  · have hprogression : ∀ᵐ p ∂σ,
        IsErdosProgression symbolicShift (symbolicPoint A) p.1 p.2 := by
      filter_upwards [hjoin.2.2] with p hp
      exact isErdosProgression_of_supportGeneric
        symbolicShift (symbolicPoint A) p.1 p.2 (component p) hp.1 hp.2
    have hsaturationMap : ∀ᵐ x ∂Measure.map Prod.snd σ,
        x ∈ ⋃ t : ℕ, shiftedOriginCylinder t :=
      hjoin.2.1.ae_le hsaturation
    have hsaturationPair : ∀ᵐ p ∂σ,
        p.2 ∈ ⋃ t : ℕ, shiftedOriginCylinder t :=
      ae_of_ae_map measurable_snd.aemeasurable hsaturationMap
    exact hprogression.and hsaturationPair

theorem forwardSaturation_originCylinder :
    forwardSaturation symbolicShift originCylinder =
      ⋃ t : ℕ, shiftedOriginCylinder t := rfl

/-- In the ergodic case the saturation hypothesis required above follows
from positivity of the cylinder automatically. -/
theorem progressionMeasure_of_ergodic_kmrrJoining {A : Set ℕ}
    {μ : Measure SymbolicSpace} [IsFiniteMeasure μ]
    {σ : Measure (SymbolicSpace × SymbolicSpace)}
    {component : SymbolicSpace × SymbolicSpace →
      Measure (SymbolicSpace × SymbolicSpace)}
    (hT : Ergodic symbolicShift μ)
    (hjoin : IsKMRRJoining A μ σ component)
    (hμorigin : 0 < μ originCylinder) :
    IsPointedProgressionMeasure A σ := by
  apply progressionMeasure_of_kmrrJoining hjoin hμorigin
  rw [← forwardSaturation_originCylinder]
  exact ae_mem_forwardSaturation_of_ergodic hT
    isClopen_originCylinder.isOpen.measurableSet (ne_of_gt hμorigin)

/-- Positive mass and the two almost-everywhere properties select the
pointed topological configuration needed by the extraction theorem. -/
theorem pointedProgression_of_progressionMeasure {A : Set ℕ}
    {σ : MeasureTheory.Measure (SymbolicSpace × SymbolicSpace)}
    (hσ : IsPointedProgressionMeasure A σ) :
    HasPointedKMRRProgression A := by
  let F : Set (SymbolicSpace × SymbolicSpace) :=
    originCylinder ×ˢ (Set.univ : Set SymbolicSpace)
  have hF : MeasurableSet F :=
    isClopen_originCylinder.isOpen.measurableSet.prod MeasurableSet.univ
  have hFne : σ F ≠ 0 := ne_of_gt hσ.1
  let : NeBot (ae (σ.restrict F)) := (ae_restrict_neBot.mpr hFne)
  have hmem : ∀ᵐ p ∂σ.restrict F, p ∈ F := ae_restrict_mem hF
  have hproperties : ∀ᵐ p ∂σ.restrict F,
      IsErdosProgression symbolicShift (symbolicPoint A) p.1 p.2 ∧
        p.2 ∈ ⋃ t : ℕ, shiftedOriginCylinder t :=
    ae_restrict_of_ae hσ.2
  obtain ⟨p, hpF, hprog, hsaturation⟩ := (hmem.and hproperties).exists
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hsaturation
  exact ⟨t, p.1, p.2, hpF.1, ht, hprog⟩

/-- The elementary extraction step in KMRR: an Erdős progression whose last
two coordinates lie in `U` and `V` yields infinitely many return times to `U`
whose distinct pairwise sums are return times to `V`. -/
theorem erdosProgression_extract {X : Type*} [TopologicalSpace X]
    (T : X → X) (hT : Continuous T) (x₀ x₁ x₂ : X)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ V)
    (hprog : IsErdosProgression T x₀ x₁ x₂) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ returnTimes T x₀ U ∧
      ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∈ returnTimes T x₀ V := by
  classical
  obtain ⟨c, hc, hc_lim⟩ := hprog
  let P : ℕ → Prop := fun b =>
    b ∈ Set.range c ∧ T^[b] x₀ ∈ U ∧ T^[b] x₁ ∈ V
  let r : ℕ → ℕ → Prop := fun b b' => b < b' ∧ T^[b + b'] x₀ ∈ V
  have hext : ∀ s : Finset ℕ, (∀ b ∈ s, P b) →
      ∃ b', P b' ∧ ∀ b ∈ s, r b b' := by
    intro s hs
    let W : Set (X × X) :=
      (U ∩ ⋂ b ∈ s, (T^[b]) ⁻¹' V) ×ˢ V
    have hW_open : IsOpen W := by
      apply IsOpen.prod
      · exact hU.inter (isOpen_biInter_finset fun b _ => hV.preimage (hT.iterate b))
      · exact hV
    have hW_mem : (x₁, x₂) ∈ W := by
      refine ⟨⟨hx₁, ?_⟩, hx₂⟩
      simp only [mem_iInter]
      intro b
      simp only [mem_preimage]
      intro hb
      exact (hs b hb).2.2
    have hevW : ∀ᶠ n in atTop,
        (T^[c n] x₀, T^[c n] x₁) ∈ W :=
      hc_lim (hW_open.mem_nhds hW_mem)
    have hc_top : Tendsto c atTop atTop := hc.tendsto_atTop
    have hevLarge : ∀ᶠ n in atTop, ∀ b ∈ s, b < c n := by
      let M := s.sup id
      filter_upwards [hc_top.eventually (eventually_ge_atTop (M + 1))] with n hn b hb
      exact lt_of_le_of_lt (Finset.le_sup (f := id) hb) hn
    obtain ⟨n, hnW, hnLarge⟩ :
        ∃ n, (T^[c n] x₀, T^[c n] x₁) ∈ W ∧ ∀ b ∈ s, b < c n := by
      exact (hevW.and hevLarge).exists
    refine ⟨c n, ?_, ?_⟩
    · refine ⟨⟨n, rfl⟩, hnW.1.1, hnW.2⟩
    · intro b hb
      refine ⟨hnLarge b hb, ?_⟩
      have hbpre : T^[c n] x₀ ∈ (T^[b]) ⁻¹' V := by
        exact (Set.mem_iInter₂.mp hnW.1.2) b hb
      simpa only [Set.mem_preimage, Function.iterate_add_apply] using hbpre
  obtain ⟨f, hfP, hfr⟩ := exists_seq_of_forall_finset_exists P r hext
  have hf_strict : StrictMono f := by
    intro m n hmn
    exact (hfr m n hmn).1
  refine ⟨Set.range f, Set.infinite_range_of_injective hf_strict.injective, ?_, ?_⟩
  · rintro b ⟨n, rfl⟩
    exact (hfP n).2.1
  · rintro b₁ ⟨i, rfl⟩ b₂ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (congrArg f h)
    rcases lt_or_gt_of_ne hij' with hij | hji
    · exact (hfr i j hij).2
    · simpa [returnTimes, Nat.add_comm] using (hfr j i hji).2

/-- The pointed KMRR progression in the symbolic system already implies the
complete combinatorial conclusion with a natural shift. -/
theorem exists_natShift_configuration_of_pointedProgression {A : Set ℕ}
    (h : HasPointedKMRRProgression A) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ t : ℕ,
      ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ + t ∈ A := by
  rcases h with ⟨t, x₁, x₂, hx₁, hx₂, hprog⟩
  obtain ⟨B, hBinf, hBreturn, hBpairs⟩ := erdosProgression_extract
    symbolicShift continuous_symbolicShift (symbolicPoint A) x₁ x₂
    isClopen_originCylinder.isOpen (isOpen_shiftedOriginCylinder t)
    hx₁ hx₂ hprog
  refine ⟨B, hBinf, ?_, t, ?_⟩
  · simpa only [returnTimes_symbolicPoint] using hBreturn
  · intro b₁ hb₁ b₂ hb₂ hne
    have hp := hBpairs b₁ hb₁ b₂ hb₂ hne
    rw [returnTimes_shiftedOriginCylinder] at hp
    simpa only [Set.mem_ofPred_eq, Nat.add_assoc] using hp

/-- Conversion of the pointed symbolic conclusion to the literal integer
shift formulation on the Erdős Problems page. -/
theorem conclusion_of_pointedProgression {A : Set ℕ}
    (h : HasPointedKMRRProgression A) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ HasTranslatedRestrictedPairSums A B := by
  obtain ⟨B, hBinf, hBA, t, hpairs⟩ :=
    exists_natShift_configuration_of_pointedProgression h
  refine ⟨B, hBinf, hBA, (t : ℤ), ?_⟩
  intro b₁ hb₁ b₂ hb₂ hne
  refine ⟨b₁ + b₂ + t, hpairs b₁ hb₁ b₂ hb₂ hne, ?_⟩
  push_cast
  rfl

/-! ### The ultrafilter interface to the analytic core -/

/-- The ultrafilter configuration produced by the analytic part of KMRR. -/
def IsKMRRWitness (A : Set ℕ) (p : Ultrafilter ℕ) (t : ℕ) : Prop :=
  (p : Filter ℕ) ≤ cofinite ∧ A ∈ p ∧
    {b : ℕ | {b' : ℕ | b + b' + t ∈ A} ∈ p} ∈ p

/-- A KMRR ultrafilter witness gives the desired infinite restricted
pair-sum configuration (with a nonnegative shift). -/
theorem IsKMRRWitness.extract {A : Set ℕ} {p : Ultrafilter ℕ} {t : ℕ}
    (h : IsKMRRWitness A p t) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ + t ∈ A := by
  classical
  rcases h with ⟨hfree, hA, hpartners⟩
  let C : Set ℕ := {b : ℕ | {b' : ℕ | b + b' + t ∈ A} ∈ p}
  let P : ℕ → Prop := fun b => b ∈ A ∧ b ∈ C
  let r : ℕ → ℕ → Prop := fun b b' => b < b' ∧ b + b' + t ∈ A
  have hext : ∀ s : Finset ℕ, (∀ b ∈ s, P b) →
      ∃ b', P b' ∧ ∀ b ∈ s, r b b' := by
    intro s hs
    let M := s.sup id
    have htail : ∀ᶠ n in p, M < n := by
      apply hfree
      rw [mem_cofinite]
      exact (Set.finite_Iic M).subset (by intro n hn; simpa using Nat.le_of_not_gt hn)
    have hsections : ∀ᶠ b' in p, ∀ b ∈ s, b + b' + t ∈ A := by
      apply s.eventually_all.2
      intro b hb
      exact (hs b hb).2
    have hlarge : ∀ᶠ b' in p,
        b' ∈ A ∧ b' ∈ C ∧ M < b' ∧ ∀ b ∈ s, b + b' + t ∈ A := by
      filter_upwards [hA, hpartners, htail, hsections] with b' hbA hbC hbM hbsec
      exact ⟨hbA, hbC, hbM, hbsec⟩
    obtain ⟨b', hbA, hbC, hbM, hbsec⟩ := hlarge.exists
    refine ⟨b', ⟨hbA, hbC⟩, ?_⟩
    intro b hb
    exact ⟨lt_of_le_of_lt (Finset.le_sup (f := id) hb) hbM, hbsec b hb⟩
  obtain ⟨f, hfP, hfr⟩ := exists_seq_of_forall_finset_exists P r hext
  have hf_strict : StrictMono f := fun i j hij => (hfr i j hij).1
  refine ⟨Set.range f, Set.infinite_range_of_injective hf_strict.injective, ?_, ?_⟩
  · rintro b ⟨i, rfl⟩
    exact (hfP i).1
  · rintro b₁ ⟨i, rfl⟩ b₂ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun e => hij (congrArg f e)
    rcases lt_or_gt_of_ne hij' with hij | hji
    · exact (hfr i j hij).2
    · simpa only [Nat.add_comm] using (hfr j i hji).2

/-- Conversion of the nonnegative-shift KMRR witness to the literal integer
shift formulation used on the Erdős Problems page. -/
theorem conclusion_of_kmrrWitness {A : Set ℕ}
    (h : ∃ p : Ultrafilter ℕ, ∃ t : ℕ, IsKMRRWitness A p t) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ HasTranslatedRestrictedPairSums A B := by
  obtain ⟨p, t, hp⟩ := h
  obtain ⟨B, hBinf, hBA, hpairs⟩ := hp.extract
  refine ⟨B, hBinf, hBA, (t : ℤ), ?_⟩
  intro b₁ hb₁ b₂ hb₂ hne
  refine ⟨b₁ + b₂ + t, hpairs b₁ hb₁ b₂ hb₂ hne, ?_⟩
  push_cast
  rfl

end

end Erdos656
namespace Erdos656

open Filter Function Set Topology MeasureTheory
open scoped ENNReal Pointwise Topology

def diagonalTransform {X : Type*} (T : X → X) : X × X → X × X :=
  fun p ↦ (T p.1, T p.2)

@[simp] theorem diagonalTransform_apply {X : Type*} (T : X → X) (p : X × X) :
    diagonalTransform T p = (T p.1, T p.2) := rfl

@[simp] theorem diagonalTransform_iterate_apply {X : Type*} (T : X → X)
    (n : ℕ) (p : X × X) :
    (diagonalTransform T)^[n] p = (T^[n] p.1, T^[n] p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change (T (T^[n] p.1), T (T^[n] p.2)) = _
      simp only [Function.iterate_succ_apply']

theorem continuous_diagonalTransform {X : Type*} [TopologicalSpace X]
    {T : X → X} (hT : Continuous T) : Continuous (diagonalTransform T) := by
  unfold diagonalTransform
  exact hT.comp continuous_fst |>.prodMk (hT.comp continuous_snd)

noncomputable def componentMoment {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (component : X × X → ProbabilityMeasure (X × X))
    (f : BoundedContinuousFunction (X × X) ℝ) (p : X × X) : ℝ :=
  ∫ q, f q ∂(component p : Measure (X × X))

theorem continuous_componentMoment
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace (X × X)]
    {component : X × X → ProbabilityMeasure (X × X)}
    (hcomponent : Continuous component)
    (f : BoundedContinuousFunction (X × X) ℝ) :
    Continuous (componentMoment component f) := by
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hcomponent

theorem componentMoment_diagonal_iterate
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (T : X → X)
    (component : X × X → ProbabilityMeasure (X × X))
    (hinv : ∀ p, component (diagonalTransform T p) = component p)
    (f : BoundedContinuousFunction (X × X) ℝ)
    (n : ℕ) (p : X × X) :
    componentMoment component f ((diagonalTransform T)^[n] p) =
      componentMoment component f p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (∫ q, f q ∂(component (diagonalTransform T
        ((diagonalTransform T)^[n] p)) : Measure (X × X))) = _
      rw [hinv]
      exact ih

theorem tendstoInMeasure_comp_measurePreserving_const
    {X E : Type*} [MeasurableSpace X] [PseudoEMetricSpace E]
    {mu : Measure X} {f : ℕ → X → E} {c : E}
    (h : TendstoInMeasure mu f atTop (fun _ ↦ c))
    (S : ℕ → X → X)
    (hS : ∀ n, MeasurePreserving (S n) mu mu) :
    TendstoInMeasure mu (fun n x ↦ f n (S n x)) atTop (fun _ ↦ c) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (h ε hε) (Eventually.of_forall fun _ ↦ zero_le) ?_
  exact Eventually.of_forall fun n ↦ by
    have hsub : {x | ε ≤ edist (f n (S n x)) c} ⊆
        S n ⁻¹' {y | ε ≤ edist (f n y) c} := by
      intro x hx
      exact hx
    exact (measure_mono hsub).trans ((hS n).measure_preimage_le _)

theorem tendstoInMeasure_of_dist_le_error_add
    {X E : Type*} [MeasurableSpace X] [PseudoMetricSpace E]
    {mu : Measure X} {F : ℕ → X → E} {g : X → E}
    {err : ℕ → X → ℝ} {delta : ℕ → ℝ}
    (herrNonneg : ∀ n x, 0 ≤ err n x)
    (herr : TendstoInMeasure mu err atTop (fun _ ↦ 0))
    (hdelta : Tendsto delta atTop (nhds 0))
    (hle : ∀ᶠ n in atTop, ∀ x,
      dist (F n x) (g x) ≤ err n x + delta n) :
    TendstoInMeasure mu F atTop g := by
  rw [tendstoInMeasure_iff_dist]
  intro eps heps
  have herrMeasure : Tendsto
      (fun n ↦ mu {x | eps / 2 ≤ dist (err n x) 0}) atTop (nhds 0) :=
    (tendstoInMeasure_iff_dist.mp herr) (eps / 2) (half_pos heps)
  have hdeltaSmall : ∀ᶠ n in atTop, delta n < eps / 2 :=
    hdelta.eventually (isOpen_Iio.mem_nhds (half_pos heps))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds herrMeasure (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hdeltaSmall, hle] with n hn hnle
  apply measure_mono
  intro x hx
  change eps ≤ dist (F n x) (g x) at hx
  have hlarge : eps / 2 ≤ err n x := by
    linarith [hnle x]
  change eps / 2 ≤ dist (err n x) 0
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (herrNonneg n x)] using hlarge

/-- A support-generic orbit can be shifted so that finitely many finite
pair averages and component moments are uniformly close to their values
over a prescribed support point. -/
theorem exists_uniform_pair_transfer_start
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompactSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T) (a b : X)
    (mu : Measure X)
    (horbit : IsSupportGeneric (fun n ↦ T^[n] a) mu)
    (hb : b ∈ mu.support)
    (component : X × X → ProbabilityMeasure (X × X))
    (hcomponent : Continuous component)
    (G : ℕ → BoundedContinuousFunction (X × X) ℝ)
    (m L : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : ℕ, ∀ j < m + 1, ∀ x : X,
      dist
          (birkhoffAverage ℝ (diagonalTransform T) (G j) L (b, x))
          (birkhoffAverage ℝ (diagonalTransform T) (G j) L
            (T^[s] a, x)) < eps ∧
        dist (componentMoment component (G j) (b, x))
          (componentMoment component (G j) (T^[s] a, x)) < eps := by
  have hfinite : ∀ j ∈ Finset.range (m + 1),
      ∀ᶠ y in 𝓝 b, ∀ x : X,
        dist
            (birkhoffAverage ℝ (diagonalTransform T) (G j) L (b, x))
            (birkhoffAverage ℝ (diagonalTransform T) (G j) L (y, x)) < eps ∧
          dist (componentMoment component (G j) (b, x))
            (componentMoment component (G j) (y, x)) < eps := by
    intro j hj
    have havgContinuous : Continuous (fun p : X × X ↦
        birkhoffAverage ℝ (diagonalTransform T) (G j) L p) :=
      continuous_birkhoffAverage_of_continuous
        (diagonalTransform T) (continuous_diagonalTransform hT)
        (G j) (G j).continuous L
    have havgUniform : TendstoUniformly
        (fun y x ↦ birkhoffAverage ℝ (diagonalTransform T) (G j)
          L (y, x))
        (fun x ↦ birkhoffAverage ℝ (diagonalTransform T) (G j)
          L (b, x)) (𝓝 b) :=
      havgContinuous.tendstoUniformly _ b
    have hmomentContinuous : Continuous (componentMoment component (G j)) :=
      continuous_componentMoment hcomponent (G j)
    have hmomentUniform : TendstoUniformly
        (fun y x ↦ componentMoment component (G j) (y, x))
        (fun x ↦ componentMoment component (G j) (b, x)) (𝓝 b) :=
      hmomentContinuous.tendstoUniformly _ b
    filter_upwards
      [(Metric.tendstoUniformly_iff.mp havgUniform eps heps),
        (Metric.tendstoUniformly_iff.mp hmomentUniform eps heps)]
      with y hyavg hymoment
    exact fun x ↦ ⟨hyavg x, hymoment x⟩
  have hall : ∀ᶠ y in 𝓝 b, ∀ j < m + 1, ∀ x : X,
      dist
          (birkhoffAverage ℝ (diagonalTransform T) (G j) L (b, x))
          (birkhoffAverage ℝ (diagonalTransform T) (G j) L (y, x)) < eps ∧
        dist (componentMoment component (G j) (b, x))
          (componentMoment component (G j) (y, x)) < eps := by
    simpa only [Finset.mem_range] using
      ((Finset.eventually_all (Finset.range (m + 1))).2 hfinite :
        ∀ᶠ y in 𝓝 b, ∀ j ∈ Finset.range (m + 1), ∀ x : X,
          dist
              (birkhoffAverage ℝ (diagonalTransform T) (G j) L (b, x))
              (birkhoffAverage ℝ (diagonalTransform T) (G j) L (y, x)) < eps ∧
            dist (componentMoment component (G j) (b, x))
              (componentMoment component (G j) (y, x)) < eps)
  have hfreq : ∃ᶠ s in atTop, ∀ j < m + 1, ∀ x : X,
      dist
          (birkhoffAverage ℝ (diagonalTransform T) (G j) L (b, x))
          (birkhoffAverage ℝ (diagonalTransform T) (G j) L
            (T^[s] a, x)) < eps ∧
        dist (componentMoment component (G j) (b, x))
          (componentMoment component (G j) (T^[s] a, x)) < eps := by
    have hf := (mapClusterPt_iff_frequently.mp (horbit b hb))
      {y | ∀ j < m + 1, ∀ x : X,
        dist
            (birkhoffAverage ℝ (diagonalTransform T) (G j) L (b, x))
            (birkhoffAverage ℝ (diagonalTransform T) (G j) L (y, x)) < eps ∧
          dist (componentMoment component (G j) (b, x))
            (componentMoment component (G j) (y, x)) < eps} hall
    simpa only [Set.mem_ofPred_eq] using hf
  exact hfreq.exists

/-- Generic-pair transfer, in the continuous-component form used by KMRR.
If almost every pair over one support point is prefix-generic for its
component, then a support-generic pointed orbit admits one common sequence
of growing interval blocks on which almost every pair is generic for the
component indexed by that pair. -/
theorem exists_weaklyGeneric_pair_orbit_blocks
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompactSpace X] [BorelSpace X] [SecondCountableTopology X]
    (T : X → X) (hT : Continuous T) (a b : X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hTmu : MeasurePreserving T mu mu)
    (horbit : IsSupportGeneric (fun n ↦ T^[n] a) mu)
    (hb : b ∈ mu.support)
    (baseLength : ℕ → ℕ) (hbaseLength : Tendsto baseLength atTop atTop)
    (component : X × X → ProbabilityMeasure (X × X))
    (hcomponent : Continuous component)
    (hinv : ∀ p, component (diagonalTransform T p) = component p)
    (htypical : ∀ᵐ x ∂mu,
      ∀ f : BoundedContinuousFunction (X × X) ℝ,
        Tendsto
          (fun m ↦ birkhoffAverage ℝ (diagonalTransform T) f (baseLength m) (b, x))
          atTop (nhds (componentMoment component f (b, x)))) :
    ∃ start length : ℕ → ℕ,
      Tendsto length atTop atTop ∧
        ∀ᵐ x ∂mu, IsWeaklyGenericAlong
          (fun n ↦ (T^[n] a, T^[n] x))
          (component (a, x) : Measure (X × X))
          (orbitIntervalBlocks start length) := by
  let : Nonempty (X × X) := ⟨(a, b)⟩
  let : TopologicalSpace.SeparableSpace
      (BoundedContinuousFunction (X × X) ℝ) := by
    let e := ContinuousMap.isometryEquivBoundedOfCompact (X × X) ℝ
    exact e.surjective.denseRange.separableSpace e.continuous
  obtain ⟨G, hG⟩ := TopologicalSpace.exists_dense_seq
      (BoundedContinuousFunction (X × X) ℝ)
  have hstartExists (m : ℕ) :
      ∃ s : ℕ, ∀ j < m + 1, ∀ x : X,
        dist
            (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m) (b, x))
            (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
              (T^[s] a, x)) < ((m + 1 : ℕ) : ℝ)⁻¹ ∧
          dist (componentMoment component (G j) (b, x))
            (componentMoment component (G j) (T^[s] a, x)) <
              ((m + 1 : ℕ) : ℝ)⁻¹ := by
    exact exists_uniform_pair_transfer_start T hT a b mu horbit hb
      component hcomponent G m (baseLength m) (by positivity)
  let start₀ : ℕ → ℕ := fun m ↦ (hstartExists m).choose
  have hstart₀ (m : ℕ) : ∀ j < m + 1, ∀ x : X,
      dist
          (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m) (b, x))
          (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
            (T^[start₀ m] a, x)) < ((m + 1 : ℕ) : ℝ)⁻¹ ∧
        dist (componentMoment component (G j) (b, x))
          (componentMoment component (G j) (T^[start₀ m] a, x)) <
            ((m + 1 : ℕ) : ℝ)⁻¹ :=
    (hstartExists m).choose_spec
  let baseError : ℕ → ℕ → X → ℝ := fun j m x ↦
    dist
      (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m) (b, x))
      (componentMoment component (G j) (b, x))
  have hbaseError (j : ℕ) : TendstoInMeasure mu (baseError j) atTop
      (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro m
      have havg : Continuous (fun p : X × X ↦
          birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m) p) :=
        continuous_birkhoffAverage_of_continuous
          (diagonalTransform T) (continuous_diagonalTransform hT)
          (G j) (G j).continuous (baseLength m)
      have havgSlice : Continuous (fun x : X ↦
          birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m) (b, x)) :=
        havg.comp (continuous_const.prodMk continuous_id)
      have hmomentSlice : Continuous (fun x : X ↦
          componentMoment component (G j) (b, x)) :=
        (continuous_componentMoment hcomponent (G j)).comp
          (continuous_const.prodMk continuous_id)
      exact (havgSlice.dist hmomentSlice).aestronglyMeasurable
    · filter_upwards [htypical] with x hx
      have hc : Tendsto
          (fun _ : ℕ ↦ componentMoment component (G j) (b, x))
          atTop (nhds (componentMoment component (G j) (b, x))) :=
        tendsto_const_nhds
      have hdist := (hx (G j)).dist hc
      simpa only [baseError, dist_self] using hdist
  let shiftedError : ℕ → ℕ → X → ℝ := fun j m x ↦
    baseError j m (T^[start₀ m] x)
  have hshiftedError (j : ℕ) : TendstoInMeasure mu (shiftedError j) atTop
      (fun _ ↦ 0) := by
    exact tendstoInMeasure_comp_measurePreserving_const (hbaseError j)
      (fun m ↦ T^[start₀ m]) (fun m ↦ hTmu.iterate (start₀ m))
  let actual : ℕ → ℕ → X → ℝ := fun j m x ↦
    birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
      (T^[start₀ m] a, T^[start₀ m] x)
  let target : ℕ → X → ℝ := fun j x ↦
    componentMoment component (G j) (a, x)
  have hactual (j : ℕ) : TendstoInMeasure mu (actual j) atTop (target j) := by
    apply tendstoInMeasure_of_dist_le_error_add
      (err := shiftedError j)
      (delta := fun m ↦ 2 * ((m + 1 : ℕ) : ℝ)⁻¹)
    · exact fun m x ↦ dist_nonneg
    · exact hshiftedError j
    · simpa only [Nat.cast_add, Nat.cast_one, one_div, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    · filter_upwards [eventually_gt_atTop j] with m hm
      intro x
      have hjm : j < m + 1 := Nat.lt_add_right 1 hm
      have hclose := hstart₀ m j hjm (T^[start₀ m] x)
      have hmomentInv :
          componentMoment component (G j)
              (T^[start₀ m] a, T^[start₀ m] x) =
            target j x := by
        rw [show (T^[start₀ m] a, T^[start₀ m] x) =
            (diagonalTransform T)^[start₀ m] (a, x) by
              simp only [diagonalTransform_iterate_apply]]
        exact componentMoment_diagonal_iterate T component hinv (G j)
          (start₀ m) (a, x)
      have htri := dist_triangle4
        (actual j m x)
        (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
          (b, T^[start₀ m] x))
        (componentMoment component (G j) (b, T^[start₀ m] x))
        (target j x)
      dsimp only [actual, shiftedError, baseError] at htri ⊢
      calc
        dist
            (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
              (T^[start₀ m] a, T^[start₀ m] x))
            (target j x) ≤
            dist
                (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
                  (T^[start₀ m] a, T^[start₀ m] x))
                (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
                  (b, T^[start₀ m] x)) +
              dist
                (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
                  (b, T^[start₀ m] x))
                (componentMoment component (G j) (b, T^[start₀ m] x)) +
              dist
                (componentMoment component (G j) (b, T^[start₀ m] x))
                (target j x) := htri
        _ ≤ shiftedError j m x + 2 * ((m + 1 : ℕ) : ℝ)⁻¹ := by
          dsimp only [shiftedError, baseError]
          rw [← hmomentInv]
          rw [dist_comm
            (birkhoffAverage ℝ (diagonalTransform T) (G j) (baseLength m)
              (T^[start₀ m] a, T^[start₀ m] x))]
          linarith [hclose.1, hclose.2]
  obtain ⟨sub, hsubTop, hsubAE⟩ :=
    exists_diagonal_tendsto_ae actual target hactual
  let start : ℕ → ℕ := fun n ↦ start₀ (sub n)
  let length : ℕ → ℕ := fun n ↦ baseLength (sub n)
  refine ⟨start, length, ?_, ?_⟩
  · exact hbaseLength.comp hsubTop
  · filter_upwards [hsubAE] with x hx
    have hall : ∀ f : BoundedContinuousFunction (X × X) ℝ,
        Tendsto
          (fun n ↦ birkhoffAverage ℝ (diagonalTransform T) f (length n)
            ((diagonalTransform T)^[start n] (a, x)))
          atTop (nhds (componentMoment component f (a, x))) := by
      intro f
      apply Metric.tendsto_atTop.2
      intro eps heps
      obtain ⟨j, hj⟩ := hG.exists_dist_lt f (show 0 < eps / 3 by positivity)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hx j) (eps / 3) (by positivity)
      refine ⟨N, fun n hn ↦ ?_⟩
      have havg : dist
            (birkhoffAverage ℝ (diagonalTransform T) f (length n)
              ((diagonalTransform T)^[start n] (a, x)))
            (birkhoffAverage ℝ (diagonalTransform T) (G j) (length n)
              ((diagonalTransform T)^[start n] (a, x))) ≤ ‖f - G j‖ := by
        simpa only [Real.dist_eq] using
          abs_birkhoffAverage_sub_le_norm (diagonalTransform T) f (G j)
            (length n) ((diagonalTransform T)^[start n] (a, x))
      have hint : dist (componentMoment component (G j) (a, x))
            (componentMoment component f (a, x)) ≤ ‖f - G j‖ := by
        rw [Real.dist_eq, abs_sub_comm]
        exact abs_integral_sub_le_norm (component (a, x) : Measure (X × X)) f (G j)
      have hnorm : ‖f - G j‖ < eps / 3 := by
        simpa only [dist_eq_norm] using hj
      have hmiddle : dist
            (birkhoffAverage ℝ (diagonalTransform T) (G j) (length n)
              ((diagonalTransform T)^[start n] (a, x)))
            (componentMoment component (G j) (a, x)) < eps / 3 := by
        simpa only [actual, target, start, length,
          diagonalTransform_iterate_apply] using hN n hn
      calc
        dist
            (birkhoffAverage ℝ (diagonalTransform T) f (length n)
              ((diagonalTransform T)^[start n] (a, x)))
            (componentMoment component f (a, x)) ≤
          dist
              (birkhoffAverage ℝ (diagonalTransform T) f (length n)
                ((diagonalTransform T)^[start n] (a, x)))
              (birkhoffAverage ℝ (diagonalTransform T) (G j) (length n)
                ((diagonalTransform T)^[start n] (a, x))) +
            dist
              (birkhoffAverage ℝ (diagonalTransform T) (G j) (length n)
                ((diagonalTransform T)^[start n] (a, x)))
              (componentMoment component (G j) (a, x)) +
            dist (componentMoment component (G j) (a, x))
              (componentMoment component f (a, x)) := dist_triangle4 _ _ _ _
        _ < eps / 3 + eps / 3 + eps / 3 := by
          exact add_lt_add (add_lt_add (havg.trans_lt hnorm) hmiddle)
            (hint.trans_lt hnorm)
        _ = eps := by ring
    have hgenericIntervals : IsGenericAlongOrbitIntervals
        (diagonalTransform T) (a, x) (component (a, x) : Measure (X × X))
        start length := by
      refine ⟨hbaseLength.comp hsubTop, ?_⟩
      intro f
      change Tendsto
        (fun k ↦ birkhoffAverage ℝ (diagonalTransform T) f (length k)
          ((diagonalTransform T)^[start k] (a, x)))
        atTop (nhds (componentMoment component f (a, x)))
      exact hall f
    have hweak := weaklyGenericAlong_orbitIntervalBlocks
      (diagonalTransform T) (a, x) (component (a, x) : Measure (X × X))
      start length hgenericIntervals
    simpa only [diagonalTransform_iterate_apply] using hweak

theorem exists_supportGeneric_pair_orbit_blocks
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompactSpace X] [T1Space X] [BorelSpace X] [SecondCountableTopology X]
    (T : X → X) (hT : Continuous T) (a b : X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hTmu : MeasurePreserving T mu mu)
    (horbit : IsSupportGeneric (fun n ↦ T^[n] a) mu)
    (hb : b ∈ mu.support)
    (baseLength : ℕ → ℕ) (hbaseLength : Tendsto baseLength atTop atTop)
    (component : X × X → ProbabilityMeasure (X × X))
    (hcomponent : Continuous component)
    (hinv : ∀ p, component (diagonalTransform T p) = component p)
    (htypical : ∀ᵐ x ∂mu,
      ∀ f : BoundedContinuousFunction (X × X) ℝ,
        Tendsto
          (fun m ↦ birkhoffAverage ℝ (diagonalTransform T) f (baseLength m) (b, x))
          atTop (nhds (componentMoment component f (b, x)))) :
    ∃ _start length : ℕ → ℕ,
      Tendsto length atTop atTop ∧
        ∀ᵐ x ∂mu, IsSupportGeneric
          (fun n ↦ (T^[n] a, T^[n] x))
          (component (a, x) : Measure (X × X)) := by
  obtain ⟨start, length, hlength, hweak⟩ :=
    exists_weaklyGeneric_pair_orbit_blocks T hT a b mu hTmu horbit hb
      baseLength hbaseLength component hcomponent hinv htypical
  refine ⟨start, length, hlength, ?_⟩
  filter_upwards [hweak] with x hx
  apply supportGeneric_of_weaklyGenericAlong_card_tendsto
    (fun n ↦ (T^[n] a, T^[n] x))
    (component (a, x) : Measure (X × X))
    (orbitIntervalBlocks start length) hx
  simpa only [card_orbitIntervalBlocks] using hlength

theorem exists_supportGeneric_pair_orbit_blocks_of_prod_ae
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompactSpace X] [T1Space X] [BorelSpace X] [SecondCountableTopology X]
    (T : X → X) (hT : Continuous T) (a : X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hTmu : MeasurePreserving T mu mu)
    (horbit : IsSupportGeneric (fun n ↦ T^[n] a) mu)
    (component : X × X → ProbabilityMeasure (X × X))
    (hcomponent : Continuous component)
    (hinv : ∀ p, component (diagonalTransform T p) = component p)
    (htypical : ∀ᵐ p ∂mu.prod mu,
      ∀ f : BoundedContinuousFunction (X × X) ℝ,
        Tendsto
          (fun m ↦ birkhoffAverage ℝ (diagonalTransform T) f (m + 1) p)
          atTop (nhds (componentMoment component f p))) :
    ∃ _start length : ℕ → ℕ,
      Tendsto length atTop atTop ∧
        ∀ᵐ x ∂mu, IsSupportGeneric
          (fun n ↦ (T^[n] a, T^[n] x))
          (component (a, x) : Measure (X × X)) := by
  have hsections : ∀ᵐ b ∂mu, ∀ᵐ x ∂mu,
      ∀ f : BoundedContinuousFunction (X × X) ℝ,
        Tendsto
          (fun m ↦ birkhoffAverage ℝ (diagonalTransform T) f (m + 1) (b, x))
          atTop (nhds (componentMoment component f (b, x))) :=
    Measure.ae_ae_of_ae_prod htypical
  obtain ⟨b, hbtypical, hbsupport⟩ :=
    (hsections.and Measure.support_mem_ae).exists
  exact exists_supportGeneric_pair_orbit_blocks T hT a b mu hTmu horbit
    hbsupport (fun m ↦ m + 1) (tendsto_add_atTop_nat 1)
    component hcomponent hinv hbtypical

/-! ### The abstract continuous Kronecker-decomposition package

The remaining analytic construction in KMRR produces exactly the data below.
Keeping its interface explicit separates the measure identities from the
generic-pair transfer proved above. -/

structure ContinuousKMRRDecomposition
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace (X × X)]
    (T : X → X) (a : X) (mu : Measure X) where
  component : X × X → ProbabilityMeasure (X × X)
  continuous_component : Continuous component
  invariant_component :
    ∀ p, component (diagonalTransform T p) = component p
  generic_component : ∃ b : X, b ∈ mu.support ∧
    ∃ baseLength : ℕ → ℕ, Tendsto baseLength atTop atTop ∧
      ∀ᵐ x ∂mu, ∀ f : BoundedContinuousFunction (X × X) ℝ,
        Tendsto
          (fun m ↦ birkhoffAverage ℝ (diagonalTransform T) f
            (baseLength m) (b, x))
          atTop (nhds (componentMoment component f (b, x)))
  sigma : ProbabilityMeasure (X × X)
  fst_sigma : Measure.map Prod.fst (sigma : Measure (X × X)) = mu
  snd_sigma_ac :
    Measure.map Prod.snd (sigma : Measure (X × X)) ≪ mu
  component_chain : ∀ᵐ p ∂(sigma : Measure (X × X)),
    component (a, p.1) = component p
  self_mem_support : ∀ᵐ p ∂(sigma : Measure (X × X)),
    p ∈ (component p : Measure (X × X)).support

def IsAbstractKMRRJoining
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (T : X → X) (a : X) (mu : Measure X)
    (sigma : Measure (X × X))
    (component : X × X → Measure (X × X)) : Prop :=
  Measure.map Prod.fst sigma = mu ∧
    Measure.map Prod.snd sigma ≪ mu ∧
      ∀ᵐ p ∂sigma,
        IsSupportGeneric (fun n : ℕ ↦ (T^[n] a, T^[n] p.1)) (component p) ∧
          p ∈ (component p).support

theorem ContinuousKMRRDecomposition.isAbstractKMRRJoining
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompactSpace X] [T1Space X] [BorelSpace X] [SecondCountableTopology X]
    (T : X → X) (hT : Continuous T) (a : X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hTmu : MeasurePreserving T mu mu)
    (horbit : IsSupportGeneric (fun n ↦ T^[n] a) mu)
    (D : ContinuousKMRRDecomposition T a mu) :
    IsAbstractKMRRJoining T a mu (D.sigma : Measure (X × X))
      (fun p ↦ (D.component p : Measure (X × X))) := by
  obtain ⟨b, hbsupport, baseLength, hbaseLength, hbtypical⟩ :=
    D.generic_component
  obtain ⟨start, length, hlength, hgeneric⟩ :=
    exists_supportGeneric_pair_orbit_blocks T hT a b mu hTmu horbit hbsupport
      baseLength hbaseLength D.component D.continuous_component
      D.invariant_component hbtypical
  have hgenericSigma : ∀ᵐ p ∂(D.sigma : Measure (X × X)),
      IsSupportGeneric (fun n : ℕ ↦ (T^[n] a, T^[n] p.1))
        (D.component (a, p.1) : Measure (X × X)) := by
    have hmap : ∀ᵐ x ∂Measure.map Prod.fst (D.sigma : Measure (X × X)),
        IsSupportGeneric (fun n : ℕ ↦ (T^[n] a, T^[n] x))
          (D.component (a, x) : Measure (X × X)) := by
      rw [D.fst_sigma]
      exact hgeneric
    exact ae_of_ae_map measurable_fst.aemeasurable hmap
  refine ⟨D.fst_sigma, D.snd_sigma_ac, ?_⟩
  filter_upwards [hgenericSigma, D.component_chain, D.self_mem_support]
    with p hp hchain hsupport
  rw [hchain] at hp
  exact ⟨hp, hsupport⟩

/-! ### Relative products over an additive compact factor -/

open ProbabilityTheory

noncomputable def translateKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (eta : Kernel Z X) (r : Z) : Kernel Z X :=
  eta.comap (fun z ↦ z + r) (measurable_id.add_const r)

@[simp] theorem translateKernel_apply
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (eta : Kernel Z X) (r z : Z) :
    translateKernel eta r z = eta (z + r) := rfl

instance instIsMarkovKernelTranslateKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r : Z) :
    IsMarkovKernel (translateKernel eta r) := by
  unfold translateKernel
  infer_instance

noncomputable def relativeProductKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (eta : Kernel Z X) (r s : Z) : Kernel Z (X × X) :=
  Kernel.prod (translateKernel eta r) (translateKernel eta s)

instance instIsMarkovKernelRelativeProductKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    IsMarkovKernel (relativeProductKernel eta r s) := by
  unfold relativeProductKernel
  infer_instance

@[simp] theorem relativeProductKernel_apply
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s z : Z) :
    relativeProductKernel eta r s z =
      (eta (z + r)).prod (eta (z + s)) := by
  rw [relativeProductKernel, Kernel.prod_apply]
  rfl

noncomputable def relativeProductProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    ProbabilityMeasure (X × X) :=
  ⟨Measure.bind m (relativeProductKernel eta r s), by infer_instance⟩

@[simp] theorem relativeProductProbability_coe
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    (relativeProductProbability m eta r s : Measure (X × X)) =
      Measure.bind m (relativeProductKernel eta r s) := rfl

theorem fst_relativeProductProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    Measure.map Prod.fst (relativeProductProbability m eta r s : Measure (X × X)) =
      Measure.bind m (translateKernel eta r) := by
  change Measure.map Prod.fst (Measure.bind m (relativeProductKernel eta r s)) = _
  rw [Measure.map_comp m (relativeProductKernel eta r s) measurable_fst]
  rw [relativeProductKernel, ← Kernel.fst_eq, Kernel.fst_prod]

theorem snd_relativeProductProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    Measure.map Prod.snd (relativeProductProbability m eta r s : Measure (X × X)) =
      Measure.bind m (translateKernel eta s) := by
  change Measure.map Prod.snd (Measure.bind m (relativeProductKernel eta r s)) = _
  rw [Measure.map_comp m (relativeProductKernel eta r s) measurable_snd]
  rw [relativeProductKernel, ← Kernel.snd_eq, Kernel.snd_prod]

/-! ### Base changes and the three-term progression kernel -/

theorem bind_map_eq_bind_comap
    {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X]
    (m : Measure Z) (f : Z → W) (hf : Measurable f)
    (eta : Kernel W X) :
    Measure.bind (Measure.map f m) eta =
      Measure.bind m (eta.comap f hf) := by
  ext s hs
  rw [Measure.bind_apply hs eta.aemeasurable,
    lintegral_map (eta.measurable_coe hs) hf,
    Measure.bind_apply hs (eta.comap f hf).aemeasurable]
  rfl

noncomputable def doubleTranslateKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) (a : Z) : Kernel Z X :=
  eta.comap (fun z ↦ a + z + z)
    ((measurable_const.add measurable_id).add measurable_id)

@[simp] theorem doubleTranslateKernel_apply
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) (a z : Z) :
    doubleTranslateKernel eta a z = eta (a + z + z) := rfl

instance instIsMarkovKernelDoubleTranslateKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [Add Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    IsMarkovKernel (doubleTranslateKernel eta a) := by
  unfold doubleTranslateKernel
  infer_instance

noncomputable def progressionKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) (a : Z) : Kernel Z (X × X) :=
  Kernel.prod (translateKernel eta a) (doubleTranslateKernel eta a)

instance instIsMarkovKernelProgressionKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    IsMarkovKernel (progressionKernel eta a) := by
  unfold progressionKernel
  infer_instance

@[simp] theorem progressionKernel_apply
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a z : Z) :
    progressionKernel eta a z =
      (eta (a + z)).prod (eta (a + z + z)) := by
  rw [progressionKernel, Kernel.prod_apply]
  simp only [translateKernel_apply, doubleTranslateKernel_apply, add_comm]

noncomputable def progressionProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    ProbabilityMeasure (X × X) :=
  ⟨Measure.bind m (progressionKernel eta a), by infer_instance⟩

@[simp] theorem progressionProbability_coe
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    (progressionProbability m eta a : Measure (X × X)) =
      Measure.bind m (progressionKernel eta a) := rfl

theorem fst_progressionProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    Measure.map Prod.fst (progressionProbability m eta a : Measure (X × X)) =
      Measure.bind m (translateKernel eta a) := by
  change Measure.map Prod.fst (Measure.bind m (progressionKernel eta a)) = _
  rw [Measure.map_comp m (progressionKernel eta a) measurable_fst]
  rw [progressionKernel, ← Kernel.fst_eq, Kernel.fst_prod]

theorem snd_progressionProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    Measure.map Prod.snd (progressionProbability m eta a : Measure (X × X)) =
      Measure.bind m (doubleTranslateKernel eta a) := by
  change Measure.map Prod.snd (Measure.bind m (progressionKernel eta a)) = _
  rw [Measure.map_comp m (progressionKernel eta a) measurable_snd]
  rw [progressionKernel, ← Kernel.snd_eq, Kernel.snd_prod]

theorem bind_translateKernel_eq
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (r : Z) :
    Measure.bind m (translateKernel eta r) = Measure.bind m eta := by
  unfold translateKernel
  rw [← bind_map_eq_bind_comap m (fun z : Z ↦ z + r)
    (measurable_id.add_const r) eta]
  rw [map_add_right_eq_self]

theorem bind_doubleTranslateKernel_ac
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) (eta : Kernel Z X) (a : Z)
    (hdouble : Measure.map (fun z : Z ↦ a + z + z) m ≪ m) :
    Measure.bind m (doubleTranslateKernel eta a) ≪ Measure.bind m eta := by
  unfold doubleTranslateKernel
  rw [← bind_map_eq_bind_comap m (fun z : Z ↦ a + z + z)
    ((measurable_const.add measurable_id).add measurable_id) eta]
  exact hdouble.comp_right eta

theorem relativeProductKernel_eq_difference_comap
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    relativeProductKernel eta r s =
      (relativeProductKernel eta 0 (s - r)).comap
        (fun z : Z ↦ z + r) (measurable_id.add_const r) := by
  ext z
  rw [Kernel.comap_apply, relativeProductKernel_apply,
    relativeProductKernel_apply]
  congr 1
  abel_nf

theorem relativeProductProbability_eq_difference
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (r s : Z) :
    relativeProductProbability m eta r s =
      relativeProductProbability m eta 0 (s - r) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.bind m (relativeProductKernel eta r s) =
    Measure.bind m (relativeProductKernel eta 0 (s - r))
  rw [relativeProductKernel_eq_difference_comap]
  rw [← bind_map_eq_bind_comap m (fun z : Z ↦ z + r)
    (measurable_id.add_const r) (relativeProductKernel eta 0 (s - r))]
  rw [map_add_right_eq_self]

theorem fst_progressionProbability_eq_base
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z) :
    Measure.map Prod.fst (progressionProbability m eta a : Measure (X × X)) =
      Measure.bind m eta := by
  rw [fst_progressionProbability, bind_translateKernel_eq]

theorem snd_progressionProbability_ac_base
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommSemigroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta] (a : Z)
    (hdouble : Measure.map (fun z : Z ↦ a + z + z) m ≪ m) :
    Measure.map Prod.snd (progressionProbability m eta a : Measure (X × X)) ≪
      Measure.bind m eta := by
  rw [snd_progressionProbability]
  exact bind_doubleTranslateKernel_ac m eta a hdouble

theorem progressionProbability_factor_relation
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableEq Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi) (a : Z)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (hdouble : Measure.map (fun z : Z ↦ a + z + z) m ≪ m) :
    ∀ᵐ p ∂(progressionProbability m eta a : Measure (X × X)),
      pi p.2 - pi p.1 = pi p.1 - a := by
  let f₁ : Z → Z := fun z ↦ a + z
  let f₂ : Z → Z := fun z ↦ a + z + z
  have hf₁ : Measurable f₁ := measurable_const.add measurable_id
  have hf₂ : Measurable f₂ :=
    (measurable_const.add measurable_id).add measurable_id
  have hfirst : ∀ᵐ z ∂m, ∀ᵐ x ∂eta (f₁ z), pi x = f₁ z := by
    have hmap : Measure.map f₁ m = m := by
      simpa only [f₁] using map_add_left_eq_self a (μ := m)
    have hP : ∀ᵐ w ∂Measure.map f₁ m, ∀ᵐ x ∂eta w, pi x = w := by
      rw [hmap]
      exact hfiber
    exact ae_of_ae_map hf₁.aemeasurable hP
  have hsecond : ∀ᵐ z ∂m, ∀ᵐ x ∂eta (f₂ z), pi x = f₂ z := by
    have hP : ∀ᵐ w ∂Measure.map f₂ m, ∀ᵐ x ∂eta w, pi x = w :=
      hdouble.ae_le hfiber
    exact ae_of_ae_map hf₂.aemeasurable hP
  have hrel : MeasurableSet
      {p : X × X | pi p.2 - pi p.1 = pi p.1 - a} := by
    apply measurableSet_eq_fun
    · exact (hpi.comp measurable_snd).sub (hpi.comp measurable_fst)
    · exact (hpi.comp measurable_fst).sub measurable_const
  have hconditional : ∀ᵐ z ∂m, ∀ᵐ p ∂progressionKernel eta a z,
      pi p.2 - pi p.1 = pi p.1 - a := by
    filter_upwards [hfirst, hsecond] with z hz₁ hz₂
    rw [progressionKernel_apply]
    rw [Measure.ae_prod_iff_ae_ae hrel]
    filter_upwards [hz₁] with x hx
    filter_upwards [hz₂] with y hy
    dsimp [f₁, f₂] at hx hy
    rw [hx, hy]
    abel
  change ∀ᵐ p ∂Measure.bind m (progressionKernel eta a), _
  exact Measure.ae_comp_of_ae_ae hrel hconditional

noncomputable def factorComponent
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (p : X × X) : ProbabilityMeasure (X × X) :=
  relativeProductProbability m eta (pi p.1) (pi p.2)

theorem factorComponent_eq_of_difference_eq
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) {p q : X × X}
    (h : pi p.2 - pi p.1 = pi q.2 - pi q.1) :
    factorComponent m eta pi p = factorComponent m eta pi q := by
  unfold factorComponent
  calc
    relativeProductProbability m eta (pi p.1) (pi p.2) =
        relativeProductProbability m eta 0 (pi p.2 - pi p.1) :=
      relativeProductProbability_eq_difference m eta _ _
    _ = relativeProductProbability m eta 0 (pi q.2 - pi q.1) := by rw [h]
    _ = relativeProductProbability m eta (pi q.1) (pi q.2) :=
      (relativeProductProbability_eq_difference m eta _ _).symm

theorem factorComponent_chain_of_factor_relation
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (a : X) {p : X × X}
    (h : pi p.2 - pi p.1 = pi p.1 - pi a) :
    factorComponent m eta pi (a, p.1) = factorComponent m eta pi p := by
  apply factorComponent_eq_of_difference_eq m eta pi
  simpa using h.symm

theorem factorComponent_chain_ae_progressionProbability
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableEq Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi) (a : X)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (hdouble : Measure.map (fun z : Z ↦ pi a + z + z) m ≪ m) :
    ∀ᵐ p ∂(progressionProbability m eta (pi a) : Measure (X × X)),
      factorComponent m eta pi (a, p.1) = factorComponent m eta pi p := by
  filter_upwards [progressionProbability_factor_relation m eta pi hpi (pi a)
    hfiber hdouble] with p hp
  exact factorComponent_chain_of_factor_relation m eta pi a hp

def HasConditionalSupportOverlap
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [Add Z]
    (m : Measure Z) (eta : Kernel Z X) (pi : X → Z)
    (sigma : Measure (X × X)) : Prop :=
  ∀ᵐ p ∂sigma, ∀ U V : Set X,
    IsOpen U → p.1 ∈ U → IsOpen V → p.2 ∈ V →
      0 < m {z : Z |
        eta (z + pi p.1) U ≠ 0 ∧ eta (z + pi p.2) V ≠ 0}

theorem mem_support_factorComponent_of_overlap
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) {p : X × X}
    (hoverlap : ∀ U V : Set X,
      IsOpen U → p.1 ∈ U → IsOpen V → p.2 ∈ V →
        0 < m {z : Z |
          eta (z + pi p.1) U ≠ 0 ∧ eta (z + pi p.2) V ≠ 0}) :
    p ∈ (factorComponent m eta pi p : Measure (X × X)).support := by
  rw [Measure.mem_support_iff_forall]
  intro W hW
  obtain ⟨U, V, hUopen, hpU, hVopen, hpV, hUV⟩ :=
    mem_nhds_prod_iff'.mp hW
  have hU : MeasurableSet U := hUopen.measurableSet
  have hV : MeasurableSet V := hVopen.measurableSet
  have hfun : Measurable (fun z : Z ↦
      eta (z + pi p.1) U * eta (z + pi p.2) V) :=
    ((eta.measurable_coe hU).comp (measurable_id.add measurable_const)).mul
      ((eta.measurable_coe hV).comp (measurable_id.add measurable_const))
  have hprod : 0 < (factorComponent m eta pi p : Measure (X × X)) (U ×ˢ V) := by
    unfold factorComponent
    change 0 < Measure.bind m
      (relativeProductKernel eta (pi p.1) (pi p.2)) (U ×ˢ V)
    rw [Measure.bind_apply (hU.prod hV)
      (relativeProductKernel eta (pi p.1) (pi p.2)).aemeasurable]
    simp_rw [relativeProductKernel_apply, Measure.prod_prod]
    rw [lintegral_pos_iff_support hfun]
    simpa only [Function.support, ne_eq, mul_eq_zero, not_or] using
      hoverlap U V hUopen hpU hVopen hpV
  exact hprod.trans_le (measure_mono hUV)

/-- The exact compact-factor hypotheses needed to assemble the KMRR
decomposition.  The later Kronecker construction supplies these fields; this
record keeps all measure-kernel bookkeeping out of the spectral argument. -/
structure ContinuousKroneckerKMRRData
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace (X × X)]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableEq Z]
    (T : X → X) (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (a : X) : Prop where
  measurable_pi : Measurable pi
  fiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z
  double_ac : Measure.map (fun z : Z ↦ pi a + z + z) m ≪ m
  continuous_component : Continuous (factorComponent m eta pi)
  invariant_component : ∀ p : X × X,
    factorComponent m eta pi (diagonalTransform T p) =
      factorComponent m eta pi p
  generic_component : ∃ b : X, b ∈ (Measure.bind m eta).support ∧
    ∃ baseLength : ℕ → ℕ, Tendsto baseLength atTop atTop ∧
      ∀ᵐ x ∂Measure.bind m eta,
        ∀ f : BoundedContinuousFunction (X × X) ℝ,
          Tendsto
            (fun n ↦ birkhoffAverage ℝ (diagonalTransform T) f
              (baseLength n) (b, x))
            atTop
              (nhds (componentMoment (factorComponent m eta pi) f (b, x)))
  support_overlap : HasConditionalSupportOverlap m eta pi
    (progressionProbability m eta (pi a) : Measure (X × X))

/-- Compact-factor data give the continuous decomposition package used by
the pointed generic-pair transfer theorem. -/
noncomputable def ContinuousKroneckerKMRRData.toContinuousKMRRDecomposition
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    [OpensMeasurableSpace (X × X)]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableEq Z]
    (T : X → X) (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (a : X)
    (h : ContinuousKroneckerKMRRData T m eta pi a) :
    ContinuousKMRRDecomposition T a (Measure.bind m eta) where
  component := factorComponent m eta pi
  continuous_component := h.continuous_component
  invariant_component := h.invariant_component
  generic_component := h.generic_component
  sigma := progressionProbability m eta (pi a)
  fst_sigma := fst_progressionProbability_eq_base m eta (pi a)
  snd_sigma_ac := snd_progressionProbability_ac_base m eta (pi a) h.double_ac
  component_chain := factorComponent_chain_ae_progressionProbability m eta pi
    h.measurable_pi a h.fiber h.double_ac
  self_mem_support := h.support_overlap.mono fun _ hp ↦
    mem_support_factorComponent_of_overlap m eta pi hp

end Erdos656
namespace Erdos656

open Filter Function Set Topology MeasureTheory
open ProbabilityTheory
open scoped ENNReal Pointwise Topology

theorem measure_inter_pos_of_three_quarters
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    {A B Q : Set X} (_hAmeas : MeasurableSet A)
    (hBmeas : MeasurableSet B) (hAQ : A ⊆ Q) (hBQ : B ⊆ Q)
    (hQpos : 0 < mu.real Q)
    (hA : (3 / 4 : ℝ) * mu.real Q < mu.real A)
    (hB : (3 / 4 : ℝ) * mu.real Q < mu.real B) :
    0 < mu (A ∩ B) := by
  rw [pos_iff_ne_zero]
  intro hinter
  have hinterReal : mu.real (A ∩ B) = 0 := by
    simp [Measure.real, hinter]
  have hunion : mu.real (A ∪ B) ≤ mu.real Q :=
    measureReal_mono (union_subset hAQ hBQ) (measure_ne_top mu Q)
  have hadd := measureReal_union_add_inter (μ := mu) (s := A) (t := B) hBmeas
  rw [hinterReal, add_zero] at hadd
  nlinarith

/-- The translate `c + Q`, represented as a preimage so measurability is
immediate from measurability of subtraction. -/
def leftAddTranslate {Z : Type*} [Sub Z] (c : Z) (Q : Set Z) : Set Z :=
  {w | w - c ∈ Q}

theorem measurableSet_leftAddTranslate
    {Z : Type*} [MeasurableSpace Z] [Sub Z] [MeasurableSub₂ Z]
    (c : Z) {Q : Set Z} (hQ : MeasurableSet Q) :
    MeasurableSet (leftAddTranslate c Q) := by
  exact (measurable_id.sub measurable_const) hQ

/-- A common sequence of Haar neighborhoods differentiates every conditional
support at every point of `L`.  The strict `3/4` form is exactly what the
support-overlap argument needs. -/
def HasConditionalSupportDensityAlong
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [Sub Z]
    (m : Measure Z) (eta : Kernel Z X) (pi : X → Z)
    (L : Set X) (Q : ℕ → Set Z) : Prop :=
  (∀ j, MeasurableSet (Q j) ∧ 0 < m.real (Q j)) ∧
    ∀ x ∈ L, ∀ U : Set X, IsOpen U → x ∈ U →
      ∀ᶠ j in atTop,
        (3 / 4 : ℝ) * m.real (Q j) <
          m.real ({z | eta z U ≠ 0} ∩ leftAddTranslate (pi x) (Q j))

theorem conditionalSupportOverlap_at_of_densityAlong
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [IsFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z)
    (L : Set X) (Q : ℕ → Set Z)
    (hdensity : HasConditionalSupportDensityAlong m eta pi L Q)
    {x₁ x₂ : X} (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L) :
    ∀ U V : Set X, IsOpen U → x₁ ∈ U → IsOpen V → x₂ ∈ V →
      0 < m {z : Z |
        eta (z + pi x₁) U ≠ 0 ∧ eta (z + pi x₂) V ≠ 0} := by
  intro U V hUopen hx₁U hVopen hx₂V
  have hU : MeasurableSet U := hUopen.measurableSet
  have hV : MeasurableSet V := hVopen.measurableSet
  have hgoodU : MeasurableSet {z : Z | eta z U ≠ 0} :=
    (eta.measurable_coe hU) (measurableSet_singleton 0).compl
  have hgoodV : MeasurableSet {z : Z | eta z V ≠ 0} :=
    (eta.measurable_coe hV) (measurableSet_singleton 0).compl
  obtain ⟨j, hjU, hjV⟩ :=
    ((hdensity.2 x₁ hx₁ U hUopen hx₁U).and
      (hdensity.2 x₂ hx₂ V hVopen hx₂V)).exists
  let beta : Z := pi x₂ - pi x₁
  let base : Set Z := leftAddTranslate (pi x₁) (Q j)
  let A : Set Z := {z | eta z U ≠ 0} ∩ base
  let B : Set Z := (fun z : Z ↦ z + beta) ⁻¹'
    ({z | eta z V ≠ 0} ∩ leftAddTranslate (pi x₂) (Q j))
  have hQmeas : MeasurableSet (Q j) := (hdensity.1 j).1
  have hbase : MeasurableSet base := by
    exact measurableSet_leftAddTranslate (pi x₁) hQmeas
  have hAmeas : MeasurableSet A := hgoodU.inter hbase
  have htargetB : MeasurableSet
      ({z : Z | eta z V ≠ 0} ∩ leftAddTranslate (pi x₂) (Q j)) :=
    hgoodV.inter (measurableSet_leftAddTranslate (pi x₂) hQmeas)
  have hBmeas : MeasurableSet B := by
    exact htargetB.preimage (measurable_id.add measurable_const)
  have hBbase : B ⊆ base := by
    intro z hz
    change z + beta ∈
      ({w : Z | eta w V ≠ 0} ∩ leftAddTranslate (pi x₂) (Q j)) at hz
    rcases hz with ⟨hzV, hzQ⟩
    change z - pi x₁ ∈ Q j
    change (z + beta) - pi x₂ ∈ Q j at hzQ
    have heq : (z + beta) - pi x₂ = z - pi x₁ := by
      dsimp [beta]
      abel
    rw [heq] at hzQ
    exact hzQ
  have hAbase : A ⊆ base := inter_subset_right
  have hbaseReal : m.real base = m.real (Q j) := by
    change (m ((fun z : Z ↦ z - pi x₁) ⁻¹' Q j)).toReal = _
    have hh := measure_preimage_add_right m (-pi x₁) (Q j)
    simpa only [sub_eq_add_neg, Measure.real] using congrArg ENNReal.toReal hh
  have hBReal : m.real B =
      m.real ({z : Z | eta z V ≠ 0} ∩
        leftAddTranslate (pi x₂) (Q j)) := by
    rw [Measure.real]
    exact congrArg ENNReal.toReal (measure_preimage_add_right m beta _)
  have hAB : 0 < m (A ∩ B) := by
    apply measure_inter_pos_of_three_quarters m hAmeas hBmeas hAbase hBbase
    · rw [hbaseReal]
      exact (hdensity.1 j).2
    · simpa only [A, base, hbaseReal] using hjU
    · rw [hBReal, hbaseReal]
      exact hjV
  let W : Set Z := {z : Z |
    eta (z + pi x₁) U ≠ 0 ∧ eta (z + pi x₂) V ≠ 0}
  have hpre : (fun z : Z ↦ z + pi x₁) ⁻¹' (A ∩ B) ⊆ W := by
    intro z hz
    change z + pi x₁ ∈ A ∩ B at hz
    rcases hz with ⟨⟨hUpos, _⟩, hVpos, _⟩
    change eta ((z + pi x₁) + beta) V ≠ 0 at hVpos
    have heq : (z + pi x₁) + beta = z + pi x₂ := by
      dsimp [beta]
      abel
    rw [heq] at hVpos
    exact ⟨hUpos, hVpos⟩
  change 0 < m W
  have hprepos : 0 < m ((fun z : Z ↦ z + pi x₁) ⁻¹' (A ∩ B)) := by
    simpa only [measure_preimage_add_right] using hAB
  exact hprepos.trans_le (measure_mono hpre)

/-- Marginal absolute continuity transports the conull differentiating set
to both coordinates of a progression measure. -/
theorem ae_conditionalSupportOverlap_of_densityAlong
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [IsFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z)
    (mu : Measure X) (L : Set X) (Q : ℕ → Set Z)
    (sigma : Measure (X × X))
    (hdensity : HasConditionalSupportDensityAlong m eta pi L Q)
    (hL : ∀ᵐ x ∂mu, x ∈ L)
    (hfst : Measure.map Prod.fst sigma = mu)
    (hsnd : Measure.map Prod.snd sigma ≪ mu) :
    ∀ᵐ p ∂sigma, ∀ U V : Set X,
      IsOpen U → p.1 ∈ U → IsOpen V → p.2 ∈ V →
        0 < m {z : Z |
          eta (z + pi p.1) U ≠ 0 ∧ eta (z + pi p.2) V ≠ 0} := by
  have hfstLmap : ∀ᵐ x ∂Measure.map Prod.fst sigma, x ∈ L := by
    rw [hfst]
    exact hL
  have hfstL : ∀ᵐ p ∂sigma, p.1 ∈ L :=
    ae_of_ae_map measurable_fst.aemeasurable hfstLmap
  have hsndLmap : ∀ᵐ x ∂Measure.map Prod.snd sigma, x ∈ L :=
    hsnd.ae_le hL
  have hsndL : ∀ᵐ p ∂sigma, p.2 ∈ L :=
    ae_of_ae_map measurable_snd.aemeasurable hsndLmap
  filter_upwards [hfstL, hsndL] with p hp₁ hp₂
  exact conditionalSupportOverlap_at_of_densityAlong
    m eta pi L Q hdensity hp₁ hp₂

end Erdos656
namespace Erdos656

open Filter Function Set Topology MeasureTheory
open scoped ENNReal Pointwise Topology

def doubleRangeSet {Z : Type*} [Add Z] : Set Z :=
  Set.range fun z : Z ↦ z + z

theorem isClosed_doubleRangeSet
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    [CompactSpace Z] [T2Space Z] : IsClosed (doubleRangeSet : Set Z) := by
  simpa [doubleRangeSet] using (isCompact_univ.image
    ((continuous_id : Continuous (fun z : Z ↦ z)).add continuous_id)).isClosed

theorem doubleRange_union_translate_eq_univ
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [CompactSpace Z] [T2Space Z]
    (m : Measure Z) [m.IsOpenPosMeasure] (alpha : Z)
    (hrot : Ergodic (fun z : Z ↦ alpha + z) m) :
    doubleRangeSet ∪ (fun z : Z ↦ alpha + z) '' doubleRangeSet = Set.univ := by
  let C : Set Z :=
    doubleRangeSet ∪ (fun z : Z ↦ alpha + z) '' doubleRangeSet
  have hD : IsClosed (doubleRangeSet : Set Z) := isClosed_doubleRangeSet
  have hC : IsClosed C := by
    apply hD.union
    exact (hD.isCompact.image
      (continuous_const.add (continuous_id : Continuous (fun z : Z ↦ z)))).isClosed
  have hrange : Set.range (fun n : ℤ ↦ n • alpha) ⊆ C := by
    rintro z ⟨n, rfl⟩
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · left
      refine ⟨k • alpha, ?_⟩
      rw [hk]
      simp only [mul_zsmul, two_zsmul]
    · right
      refine ⟨k • alpha + k • alpha, ⟨k • alpha, rfl⟩, ?_⟩
      rw [hk]
      simp only [add_zsmul, mul_zsmul, one_zsmul]
      abel
  have hdense : Dense C :=
    (DenseRange.zsmul_of_ergodic_add_left hrot).mono hrange
  have hclosure : closure C = Set.univ := hdense.closure_eq
  change C = Set.univ
  rw [← hC.closure_eq, hclosure]

noncomputable def doublePushforward
    {Z : Type*} [MeasurableSpace Z] [Add Z] [MeasurableAdd₂ Z]
    (m : Measure Z) : Measure Z :=
  Measure.map (fun z : Z ↦ z + z) m

theorem map_add_left_doublePushforward
    {Z : Type*} [MeasurableSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [Measure.IsAddLeftInvariant m] (w : Z) :
    Measure.map (fun z : Z ↦ (w + w) + z) (doublePushforward m) =
      doublePushforward m := by
  rw [doublePushforward, Measure.map_map
    (μ := m) (g := fun z : Z ↦ (w + w) + z) (f := fun z : Z ↦ z + z)
    (measurable_const.add measurable_id) (measurable_id.add measurable_id)]
  change Measure.map (fun z : Z ↦ (w + w) + (z + z)) m =
    Measure.map (fun z : Z ↦ z + z) m
  have hfun :
      (fun z : Z ↦ (w + w) + (z + z)) =
        (fun z : Z ↦ (w + z) + (w + z)) := by
    funext z
    abel
  rw [hfun]
  calc
    Measure.map (fun z : Z ↦ (w + z) + (w + z)) m =
        Measure.map (fun z : Z ↦ z + z)
          (Measure.map (fun z : Z ↦ w + z) m) := by
      rw [Measure.map_map
        (μ := m) (g := fun z : Z ↦ z + z) (f := fun z : Z ↦ w + z)
        (measurable_id.add measurable_id) (measurable_const.add measurable_id)]
      exact congrArg (fun f : Z → Z ↦ Measure.map f m) (by
        funext z
        rfl)
    _ = Measure.map (fun z : Z ↦ z + z) m := by
      rw [map_add_left_eq_self]

theorem map_add_left_comp
    {Z : Type*} [MeasurableSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (mu : Measure Z) (a b : Z) :
    Measure.map (fun z : Z ↦ a + z)
        (Measure.map (fun z : Z ↦ b + z) mu) =
      Measure.map (fun z : Z ↦ (a + b) + z) mu := by
  rw [Measure.map_map
    (μ := mu) (g := fun z : Z ↦ a + z) (f := fun z : Z ↦ b + z)
    (measurable_const.add measurable_id) (measurable_const.add measurable_id)]
  congr 1
  funext z
  dsimp
  abel

noncomputable def parityAverageMeasure
    {Z : Type*} [MeasurableSpace Z] [Add Z] [MeasurableAdd₂ Z]
    (m : Measure Z) (alpha : Z) : Measure Z :=
  (2 : ℝ≥0∞)⁻¹ •
    (doublePushforward m +
      Measure.map (fun z : Z ↦ alpha + z) (doublePushforward m))

theorem map_add_left_parityAverage_alpha
    {Z : Type*} [MeasurableSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [Measure.IsAddLeftInvariant m] (alpha : Z) :
    Measure.map (fun z : Z ↦ alpha + z)
        (parityAverageMeasure m alpha) =
      parityAverageMeasure m alpha := by
  rw [parityAverageMeasure, Measure.map_smul _
    (f := fun z : Z ↦ alpha + z) (measurable_const.add measurable_id).aemeasurable]
  rw [Measure.map_add (doublePushforward m)
    (Measure.map (fun z : Z ↦ alpha + z) (doublePushforward m))
    (f := fun z : Z ↦ alpha + z) (measurable_const.add measurable_id)]
  rw [map_add_left_comp]
  have htwo : alpha + alpha ∈ (doubleRangeSet : Set Z) :=
    ⟨alpha, rfl⟩
  have hinv : Measure.map (fun z : Z ↦ (alpha + alpha) + z)
      (doublePushforward m) = doublePushforward m :=
    map_add_left_doublePushforward m alpha
  rw [hinv]
  ac_rfl

theorem map_add_left_parityAverage_of_mem_doubleRange
    {Z : Type*} [MeasurableSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [Measure.IsAddLeftInvariant m] (alpha d : Z)
    (hd : d ∈ (doubleRangeSet : Set Z)) :
    Measure.map (fun z : Z ↦ d + z)
        (parityAverageMeasure m alpha) =
      parityAverageMeasure m alpha := by
  obtain ⟨w, rfl⟩ := hd
  rw [parityAverageMeasure, Measure.map_smul _
    (f := fun z : Z ↦ (w + w) + z) (measurable_const.add measurable_id).aemeasurable]
  change (2 : ℝ≥0∞)⁻¹ •
      Measure.map (fun z : Z ↦ (w + w) + z)
        (doublePushforward m +
          Measure.map (fun z : Z ↦ alpha + z) (doublePushforward m)) = _
  rw [Measure.map_add (doublePushforward m)
    (Measure.map (fun z : Z ↦ alpha + z) (doublePushforward m))
    (f := fun z : Z ↦ (w + w) + z) (measurable_const.add measurable_id)]
  rw [map_add_left_doublePushforward]
  rw [map_add_left_comp]
  have hcomm : (w + w) + alpha = alpha + (w + w) := add_comm _ _
  rw [hcomm, ← map_add_left_comp]
  rw [map_add_left_doublePushforward]

theorem map_add_left_parityAverage
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [MeasurableAdd₂ Z]
    [CompactSpace Z] [T2Space Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddLeftInvariant m] (alpha z : Z)
    (hrot : Ergodic (fun w : Z ↦ alpha + w) m) :
    Measure.map (fun w : Z ↦ z + w)
        (parityAverageMeasure m alpha) =
      parityAverageMeasure m alpha := by
  have hcover := doubleRange_union_translate_eq_univ m alpha hrot
  have hz : z ∈ doubleRangeSet ∪
      (fun w : Z ↦ alpha + w) '' doubleRangeSet := by
    rw [hcover]
    trivial
  rcases hz with hz | ⟨d, hd, rfl⟩
  · exact map_add_left_parityAverage_of_mem_doubleRange m alpha z hz
  · rw [show (fun w : Z ↦ (alpha + d) + w) =
        (fun w : Z ↦ alpha + w) ∘ (fun w : Z ↦ d + w) by
      funext w; dsimp; abel]
    rw [← Measure.map_map
      (μ := parityAverageMeasure m alpha)
      (g := fun w : Z ↦ alpha + w) (f := fun w : Z ↦ d + w)
      (measurable_const.add measurable_id) (measurable_const.add measurable_id)]
    rw [map_add_left_parityAverage_of_mem_doubleRange m alpha d hd]
    exact map_add_left_parityAverage_alpha m alpha

theorem parityAverageMeasure_univ
    {Z : Type*} [MeasurableSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m] (alpha : Z) :
    parityAverageMeasure m alpha Set.univ = 1 := by
  have hdouble : doublePushforward m Set.univ = 1 := by
    rw [doublePushforward, Measure.map_apply_of_aemeasurable
      (f := fun z : Z ↦ z + z)
      (measurable_id.add measurable_id).aemeasurable MeasurableSet.univ]
    simp
  have hshift :
      (Measure.map (fun z : Z ↦ alpha + z) (doublePushforward m)) Set.univ = 1 := by
    rw [Measure.map_apply_of_aemeasurable
      (f := fun z : Z ↦ alpha + z)
      (measurable_const.add measurable_id).aemeasurable MeasurableSet.univ]
    simpa using hdouble
  rw [parityAverageMeasure, Measure.smul_apply, Measure.add_apply]
  rw [hdouble, hshift]
  simp only [smul_eq_mul, one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

theorem parityAverageMeasure_eq
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [MeasurableAdd₂ Z]
    [CompactSpace Z] [T2Space Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddHaarMeasure m] (alpha : Z)
    (hrot : Ergodic (fun w : Z ↦ alpha + w) m) :
    parityAverageMeasure m alpha = m := by
  let hprob : IsProbabilityMeasure (parityAverageMeasure m alpha) :=
    ⟨parityAverageMeasure_univ m alpha⟩
  let hinv : Measure.IsAddLeftInvariant (parityAverageMeasure m alpha) :=
    ⟨fun z ↦ map_add_left_parityAverage m alpha z hrot⟩
  let hhaar : Measure.IsAddHaarMeasure (parityAverageMeasure m alpha) :=
    Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
      (parityAverageMeasure m alpha) Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    (parityAverageMeasure m alpha) m

theorem doublePushforward_absolutelyContinuous
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [MeasurableAdd₂ Z]
    [CompactSpace Z] [T2Space Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddHaarMeasure m] (alpha : Z)
    (hrot : Ergodic (fun w : Z ↦ alpha + w) m) :
    doublePushforward m ≪ m := by
  have heq := parityAverageMeasure_eq m alpha hrot
  have hac : doublePushforward m ≪ parityAverageMeasure m alpha := by
    rw [parityAverageMeasure]
    exact Measure.AbsolutelyContinuous.smul_right
      (Measure.AbsolutelyContinuous.rfl.add_right
        (Measure.map (fun z : Z ↦ alpha + z) (doublePushforward m)))
      (c := (2 : ℝ≥0∞)⁻¹) (by simp)
  simpa only [heq] using hac

theorem map_add_left_doublePushforward_absolutelyContinuous
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [MeasurableAdd₂ Z]
    [CompactSpace Z] [T2Space Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddHaarMeasure m] (alpha a : Z)
    (hrot : Ergodic (fun w : Z ↦ alpha + w) m) :
    Measure.map (fun z : Z ↦ a + z) (doublePushforward m) ≪ m := by
  have h := (MeasurableEquiv.addLeft a).measurableEmbedding.absolutelyContinuous_map
    (doublePushforward_absolutelyContinuous m alpha hrot)
  simpa only [MeasurableEquiv.coe_addLeft, map_add_left_eq_self] using h

theorem map_add_left_double_absolutelyContinuous
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [MeasurableAdd₂ Z]
    [CompactSpace Z] [T2Space Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddHaarMeasure m] (alpha a : Z)
    (hrot : Ergodic (fun w : Z ↦ alpha + w) m) :
    Measure.map (fun z : Z ↦ a + (z + z)) m ≪ m := by
  change Measure.map ((fun z : Z ↦ a + z) ∘ (fun z : Z ↦ z + z)) m ≪ m
  rw [← Measure.map_map
    (μ := m) (g := fun z : Z ↦ a + z) (f := fun z : Z ↦ z + z)
    (measurable_const.add measurable_id) (measurable_id.add measurable_id)]
  exact map_add_left_doublePushforward_absolutelyContinuous m alpha a hrot

end Erdos656
namespace Erdos656

open Filter Function Set Topology MeasureTheory Metric
open ProbabilityTheory
open scoped ENNReal Pointwise Topology ComplexConjugate

noncomputable def densityRadius (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

def haarDensityNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [Zero Z] (j : ℕ) : Set Z :=
  Metric.closedBall 0 (densityRadius j)

theorem tendsto_densityRadius :
    Tendsto densityRadius atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · change Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0)
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Eventually.of_forall fun j ↦ by
      change 0 < 1 / ((j : ℝ) + 1)
      positivity

theorem leftAddTranslate_closedBall
    {Z : Type*} [PseudoMetricSpace Z] [AddCommGroup Z]
    [IsIsometricVAdd Z Z] (c : Z) (r : ℝ) :
    leftAddTranslate c (Metric.closedBall 0 r) = Metric.closedBall c r := by
  ext z
  change dist (z - c) 0 ≤ r ↔ dist z c ≤ r
  have hdist : dist (z - c) 0 = dist z c := by
    calc
      dist (z - c) 0 = dist (c + (z - c)) (c + 0) :=
        (dist_add_left c (z - c) 0).symm
      _ = dist z c := by simp
  rw [hdist]

theorem leftAddTranslate_haarDensityNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [AddCommGroup Z]
    [IsIsometricVAdd Z Z] (c : Z) (j : ℕ) :
    leftAddTranslate c (haarDensityNeighborhood j) =
      Metric.closedBall c (densityRadius j) := by
  exact leftAddTranslate_closedBall c (densityRadius j)

theorem measurable_pos_haarDensityNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddCommGroup Z]
    (m : Measure Z) [m.IsOpenPosMeasure] [IsFiniteMeasure m] (j : ℕ) :
    MeasurableSet (haarDensityNeighborhood (Z := Z) j) ∧
      0 < m.real (haarDensityNeighborhood (Z := Z) j) := by
  constructor
  · exact measurableSet_closedBall
  · change 0 < (m (Metric.closedBall (0 : Z) (densityRadius j))).toReal
    have hsub :
        Metric.ball (0 : Z) (densityRadius j) ⊆
          Metric.closedBall (0 : Z) (densityRadius j) :=
      Metric.ball_subset_closedBall
    have hpos : 0 < m (Metric.closedBall (0 : Z) (densityRadius j)) :=
      (measure_ball_pos m (0 : Z) (by
        change 0 < 1 / ((j : ℝ) + 1)
        positivity)).trans_le (measure_mono hsub)
    exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top m _)

theorem ae_tendsto_haarDensityRatio
    {Z : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z]
    [IsIsometricVAdd Z Z]
    (m : Measure Z) [IsLocallyFiniteMeasure m]
    [IsUnifLocDoublingMeasure m] [Measure.IsAddLeftInvariant m]
    (S : Set Z) :
    ∀ᵐ z ∂m.restrict S,
      Tendsto (fun j : ℕ ↦
        m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m (haarDensityNeighborhood (Z := Z) j)) atTop (nhds 1) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div m S 1] with z hz
  have hmem : ∀ᶠ j : ℕ in atTop,
      z ∈ Metric.closedBall z (1 * densityRadius j) :=
    Eventually.of_forall fun j ↦ by
      rw [Metric.mem_closedBall]
      simp only [dist_self, one_mul]
      exact (by
        change 0 ≤ 1 / ((j : ℝ) + 1)
        positivity)
  have hballs := hz (fun _ : ℕ ↦ z) densityRadius
    tendsto_densityRadius hmem
  have heq :
      (fun j : ℕ ↦
        m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m (haarDensityNeighborhood (Z := Z) j)) =
        (fun j : ℕ ↦
          m (S ∩ Metric.closedBall z (densityRadius j)) /
            m (Metric.closedBall z (densityRadius j))) := by
    funext j
    have htranslate :
        m (leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) =
          m (haarDensityNeighborhood (Z := Z) j) := by
      change m ((fun w : Z ↦ w - z) ⁻¹'
          haarDensityNeighborhood (Z := Z) j) = _
      simpa only [sub_eq_add_neg] using
        (measure_preimage_add_right m (-z)
          (haarDensityNeighborhood (Z := Z) j))
    rw [← htranslate, leftAddTranslate_haarDensityNeighborhood]
  rw [heq]
  exact hballs

theorem ae_three_quarters_haarDensity
    {Z : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z]
    [IsIsometricVAdd Z Z]
    (m : Measure Z) [IsFiniteMeasure m] [IsLocallyFiniteMeasure m]
    [m.IsOpenPosMeasure]
    [IsUnifLocDoublingMeasure m] [Measure.IsAddLeftInvariant m]
    (S : Set Z) :
    ∀ᵐ z ∂m.restrict S, ∀ᶠ j : ℕ in atTop,
      (3 / 4 : ℝ) * m.real (haarDensityNeighborhood (Z := Z) j) <
        m.real (S ∩ leftAddTranslate z
          (haarDensityNeighborhood (Z := Z) j)) := by
  filter_upwards [ae_tendsto_haarDensityRatio m S] with z hz
  have hratio : ∀ᶠ j : ℕ in atTop,
      (3 / 4 : ℝ≥0∞) <
        m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m (haarDensityNeighborhood (Z := Z) j) :=
    (tendsto_order.mp hz).1 (3 / 4 : ℝ≥0∞) (by
      apply (ENNReal.div_lt_iff (Or.inl (by norm_num))
        (Or.inl (by norm_num))).2
      norm_num)
  filter_upwards [hratio] with j hj
  have hQpos := (measurable_pos_haarDensityNeighborhood m j).2
  have hfiniteRatio :
      m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m (haarDensityNeighborhood (Z := Z) j) ≠ ⊤ := by
    exact ENNReal.div_ne_top (measure_ne_top m _)
      (ne_of_gt (ENNReal.toReal_pos_iff.mp hQpos).1)
  have hreal :
      (3 / 4 : ℝ) <
        m.real (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m.real (haarDensityNeighborhood (Z := Z) j) := by
    have hconst : (3 / 4 : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top (by norm_num) (by norm_num)
    have h := (ENNReal.toReal_lt_toReal hconst
      hfiniteRatio).mpr hj
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Measure.real] using h
  exact (lt_div_iff₀ hQpos).mp hreal

def IsHaarDensityPoint
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [AddCommGroup Z]
    (m : Measure Z) (S : Set Z) (z : Z) : Prop :=
  Tendsto (fun j : ℕ ↦
    m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
      m (haarDensityNeighborhood (Z := Z) j)) atTop (nhds 1)

theorem three_quarters_of_isHaarDensityPoint
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddCommGroup Z]
    (m : Measure Z) [IsFiniteMeasure m] [m.IsOpenPosMeasure]
    {S : Set Z} {z : Z} (hz : IsHaarDensityPoint m S z) :
    ∀ᶠ j : ℕ in atTop,
      (3 / 4 : ℝ) * m.real (haarDensityNeighborhood (Z := Z) j) <
        m.real (S ∩ leftAddTranslate z
          (haarDensityNeighborhood (Z := Z) j)) := by
  have hratio : ∀ᶠ j : ℕ in atTop,
      (3 / 4 : ℝ≥0∞) <
        m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m (haarDensityNeighborhood (Z := Z) j) :=
    (tendsto_order.mp hz).1 (3 / 4 : ℝ≥0∞) (by
      apply (ENNReal.div_lt_iff (Or.inl (by norm_num))
        (Or.inl (by norm_num))).2
      norm_num)
  filter_upwards [hratio] with j hj
  have hQpos := (measurable_pos_haarDensityNeighborhood m j).2
  have hfiniteRatio :
      m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m (haarDensityNeighborhood (Z := Z) j) ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top m _)
      (ne_of_gt (ENNReal.toReal_pos_iff.mp hQpos).1)
  have hconst : (3 / 4 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have h := (ENNReal.toReal_lt_toReal hconst hfiniteRatio).mpr hj
  have hreal :
      (3 / 4 : ℝ) <
        m.real (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
          m.real (haarDensityNeighborhood (Z := Z) j) := by
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Measure.real] using h
  exact (lt_div_iff₀ hQpos).mp hreal

theorem measurable_haarDensityRatioAt
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [SFinite m] {S : Set Z} (hS : MeasurableSet S)
    (j : ℕ) :
    Measurable (fun z : Z ↦
      m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j)) /
        m (haarDensityNeighborhood (Z := Z) j)) := by
  let R : Set (Z × Z) :=
    {p | p.2 ∈ S ∧ p.2 - p.1 ∈ haarDensityNeighborhood (Z := Z) j}
  have hR : MeasurableSet R := by
    exact (hS.preimage measurable_snd).inter
      (measurableSet_closedBall.preimage
        (measurable_snd.sub measurable_fst))
  have hnum : Measurable (fun z : Z ↦
      m (S ∩ leftAddTranslate z (haarDensityNeighborhood (Z := Z) j))) := by
    have h := measurable_measure_prodMk_left (ν := m) hR
    convert h using 1
    funext z
    congr 1
  exact hnum.div measurable_const

theorem measurableSet_isHaarDensityPoint
    {Z : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [SFinite m] {S : Set Z} (hS : MeasurableSet S) :
    MeasurableSet {z : Z | IsHaarDensityPoint m S z} := by
  exact MeasureTheory.measurableSet_tendsto_fun
    (fun j ↦ measurable_haarDensityRatioAt m hS j) measurable_const

theorem ae_isHaarDensityPoint
    {Z : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [IsIsometricVAdd Z Z]
    (m : Measure Z) [IsLocallyFiniteMeasure m]
    [IsUnifLocDoublingMeasure m] [Measure.IsAddLeftInvariant m]
    (S : Set Z) :
    ∀ᵐ z ∂m.restrict S, IsHaarDensityPoint m S z := by
  exact ae_tendsto_haarDensityRatio m S

noncomputable def conditionalSupportBasis
    (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    ℕ → Set X :=
  (TopologicalSpace.exists_seq_basis X).choose

theorem conditionalSupportBasis_isBasis
    (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    TopologicalSpace.IsTopologicalBasis
      (Set.range (conditionalSupportBasis X)) :=
  (TopologicalSpace.exists_seq_basis X).choose_spec

theorem isOpen_conditionalSupportBasis
    (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] (i : ℕ) :
    IsOpen (conditionalSupportBasis X i) := by
  exact (conditionalSupportBasis_isBasis X).isOpen
    (Set.mem_range_self i)

def conditionalSupportDensitySet
    {Z X : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [AddCommGroup Z] [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X]
    (m : Measure Z) (eta : Kernel Z X) (pi : X → Z) : Set X :=
  {x | ∀ i : ℕ, x ∈ conditionalSupportBasis X i →
    IsHaarDensityPoint m
      {z : Z | eta z (conditionalSupportBasis X i) ≠ 0} (pi x)}

theorem measurableSet_conditionalSupportDensitySet
    {Z X : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [SFinite m] (eta : Kernel Z X)
    (pi : X → Z) (hpi : Measurable pi) :
    MeasurableSet (conditionalSupportDensitySet m eta pi) := by
  have hall : MeasurableSet (⋂ i : ℕ,
      (conditionalSupportBasis X i)ᶜ ∪ pi ⁻¹'
        {z : Z | IsHaarDensityPoint m
          {w : Z | eta w (conditionalSupportBasis X i) ≠ 0} z}) := by
    apply MeasurableSet.iInter
    intro i
    have hBopen : IsOpen (conditionalSupportBasis X i) :=
      isOpen_conditionalSupportBasis X i
    have hB : MeasurableSet (conditionalSupportBasis X i) :=
      hBopen.measurableSet
    have hS : MeasurableSet
        {z : Z | eta z (conditionalSupportBasis X i) ≠ 0} :=
      (eta.measurable_coe hB) (measurableSet_singleton 0).compl
    have hD : MeasurableSet {z : Z | IsHaarDensityPoint m
        {w : Z | eta w (conditionalSupportBasis X i) ≠ 0} z} :=
      measurableSet_isHaarDensityPoint m hS
    exact hB.compl.union (hD.preimage hpi)
  convert hall using 1
  ext x
  simp only [conditionalSupportDensitySet, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · intro h i
    by_cases hxi : x ∈ conditionalSupportBasis X i
    · exact Or.inr (h i hxi)
    · exact Or.inl hxi
  · intro h i hxi
    rcases h i with hnot | hd
    · exact (hnot hxi).elim
    · exact hd

theorem ae_basis_conditionalSupportDensity
    {Z X : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z] [IsIsometricVAdd Z Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [SFinite m] [IsLocallyFiniteMeasure m]
    [IsUnifLocDoublingMeasure m] [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z) (i : ℕ) :
    ∀ᵐ x ∂Measure.bind m eta,
      x ∈ conditionalSupportBasis X i →
        IsHaarDensityPoint m
          {z : Z | eta z (conditionalSupportBasis X i) ≠ 0} (pi x) := by
  let B : Set X := conditionalSupportBasis X i
  let S : Set Z := {z : Z | eta z B ≠ 0}
  have hBopen : IsOpen B := isOpen_conditionalSupportBasis X i
  have hB : MeasurableSet B := hBopen.measurableSet
  have hS : MeasurableSet S :=
    (eta.measurable_coe hB) (measurableSet_singleton 0).compl
  have hdBase : ∀ᵐ z ∂m, z ∈ S → IsHaarDensityPoint m S z :=
    (ae_restrict_iff' hS).mp (ae_isHaarDensityPoint m S)
  have hcond : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z,
      x ∈ B → IsHaarDensityPoint m S (pi x) := by
    filter_upwards [hdBase, hfiber] with z hz hzpi
    by_cases hzS : z ∈ S
    · have hDz := hz hzS
      filter_upwards [hzpi] with x hxpi
      intro _
      simpa only [hxpi] using hDz
    · have hzero : eta z B = 0 := not_ne_iff.mp hzS
      have hnotB : ∀ᵐ x ∂eta z, x ∉ B := by
        rw [ae_iff]
        have heq : {x : X | ¬x ∉ B} = B := by
          ext x
          simp
        rw [heq]
        exact hzero
      filter_upwards [hnotB] with x hx
      exact fun hxB ↦ (hx hxB).elim
  have hpiece : MeasurableSet {x : X |
      x ∈ B → IsHaarDensityPoint m S (pi x)} := by
    have hD : MeasurableSet {z : Z | IsHaarDensityPoint m S z} :=
      measurableSet_isHaarDensityPoint m hS
    have hu : MeasurableSet (Bᶜ ∪ pi ⁻¹'
        {z : Z | IsHaarDensityPoint m S z}) :=
      hB.compl.union (hD.preimage hpi)
    convert hu using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
      Set.mem_preimage]
    tauto
  exact Measure.ae_comp_of_ae_ae hpiece hcond

theorem ae_mem_conditionalSupportDensitySet
    {Z X : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z] [IsIsometricVAdd Z Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [SFinite m] [IsLocallyFiniteMeasure m]
    [IsUnifLocDoublingMeasure m] [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z) :
    ∀ᵐ x ∂Measure.bind m eta,
      x ∈ conditionalSupportDensitySet m eta pi := by
  exact ae_all_iff.mpr fun i ↦
    ae_basis_conditionalSupportDensity m eta pi hpi hfiber i

theorem hasConditionalSupportDensityAlong_conditionalSupportDensitySet
    {Z X : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z] [IsIsometricVAdd Z Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [IsFiniteMeasure m] [IsLocallyFiniteMeasure m]
    [m.IsOpenPosMeasure] [IsUnifLocDoublingMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) :
    HasConditionalSupportDensityAlong m eta pi
      (conditionalSupportDensitySet m eta pi)
      (haarDensityNeighborhood (Z := Z)) := by
  constructor
  · exact measurable_pos_haarDensityNeighborhood m
  · intro x hx U hUopen hxU
    obtain ⟨V, hVB, hxV, hVU⟩ :=
      (conditionalSupportBasis_isBasis X).exists_subset_of_mem_open hxU hUopen
    rcases hVB with ⟨i, rfl⟩
    have hxD : IsHaarDensityPoint m
        {z : Z | eta z (conditionalSupportBasis X i) ≠ 0} (pi x) := by
      exact hx i hxV
    have hsmall := three_quarters_of_isHaarDensityPoint m hxD
    filter_upwards [hsmall] with j hj
    apply hj.trans_le
    apply measureReal_mono
    · rintro z ⟨hz, hzQ⟩
      refine ⟨?_, hzQ⟩
      intro hzero
      exact hz (measure_mono_null hVU hzero)
    · exact measure_ne_top m _

theorem conditionalSupportOverlap_of_fiberDensity
    {Z X : Type*} [PseudoMetricSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z] [MeasurableEq Z]
    [IsIsometricVAdd Z Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.IsOpenPosMeasure] [IsUnifLocDoublingMeasure m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (sigma : Measure (X × X))
    (hfst : Measure.map Prod.fst sigma = Measure.bind m eta)
    (hsnd : Measure.map Prod.snd sigma ≪ Measure.bind m eta) :
    HasConditionalSupportOverlap m eta pi sigma := by
  exact ae_conditionalSupportOverlap_of_densityAlong
    m eta pi (Measure.bind m eta)
      (conditionalSupportDensitySet m eta pi)
      (haarDensityNeighborhood (Z := Z)) sigma
      (hasConditionalSupportDensityAlong_conditionalSupportDensitySet m eta pi)
      (ae_mem_conditionalSupportDensitySet m eta pi hpi hfiber)
      hfst hsnd

/-! ## Countability of the Koopman point spectrum

The Kronecker factor is generated by eigenfunctions.  The first analytic
input needed to construct it is that its set of eigenvalues is countable.
This follows by normalizing one eigenvector for each eigenvalue: distinct
ones are orthogonal, hence form a uniformly separated family in separable
`L²`.
-/

noncomputable def koopmanL2Complex
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :
    Lp ℂ (2 : ℝ≥0∞) mu →L[ℂ] Lp ℂ (2 : ℝ≥0∞) mu :=
  (Lp.compMeasurePreservingₗᵢ (p := (2 : ℝ≥0∞)) ℂ T hT).toContinuousLinearMap

theorem norm_koopmanL2Complex
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (v : Lp ℂ (2 : ℝ≥0∞) mu) :
    ‖koopmanL2Complex T mu hT v‖ = ‖v‖ := by
  simp [koopmanL2Complex]

def IsKoopmanEigenvalue
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) (lambda : ℂ) : Prop :=
  ∃ v : Lp ℂ (2 : ℝ≥0∞) mu,
    v ≠ 0 ∧ koopmanL2Complex T mu hT v = lambda • v

theorem norm_eq_one_of_isKoopmanEigenvalue
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    {lambda : ℂ} (hlambda : IsKoopmanEigenvalue T mu hT lambda) :
    ‖lambda‖ = 1 := by
  obtain ⟨v, hv, hev⟩ := hlambda
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm := congrArg norm hev
  rw [norm_koopmanL2Complex, norm_smul] at hnorm
  nlinarith

theorem inner_eq_zero_of_koopman_eigenvectors
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    {lambda gamma : ℂ} {v w : Lp ℂ (2 : ℝ≥0∞) mu}
    (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hv : koopmanL2Complex T mu hT v = lambda • v)
    (hw : koopmanL2Complex T mu hT w = gamma • w)
    (hne : lambda ≠ gamma) :
    inner ℂ v w = 0 := by
  have hlambda : ‖lambda‖ = 1 :=
    norm_eq_one_of_isKoopmanEigenvalue T mu hT ⟨v, hv0, hv⟩
  have hgamma : ‖gamma‖ = 1 :=
    norm_eq_one_of_isKoopmanEigenvalue T mu hT ⟨w, hw0, hw⟩
  have hinner :=
    (Lp.compMeasurePreservingₗᵢ (p := (2 : ℝ≥0∞)) ℂ T hT).inner_map_map v w
  change inner ℂ (koopmanL2Complex T mu hT v)
      (koopmanL2Complex T mu hT w) = inner ℂ v w at hinner
  rw [hv, hw, inner_smul_left, inner_smul_right] at hinner
  have hcoeff : conj lambda * gamma ≠ 1 := by
    intro heq
    have hlambda0 : lambda ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hlambda
      norm_num at hlambda
    apply hne
    calc
      lambda = lambda * 1 := by simp
      _ = lambda * (conj lambda * gamma) := by rw [heq]
      _ = (lambda * conj lambda) * gamma := by rw [mul_assoc]
      _ = gamma := by simp [Complex.mul_conj', hlambda]
  have hprod : (conj lambda * gamma - 1) * inner ℂ v w = 0 := by
    calc
      (conj lambda * gamma - 1) * inner ℂ v w =
          (conj lambda * gamma) * inner ℂ v w - inner ℂ v w := by ring
      _ = 0 := sub_eq_zero.mpr (by simpa [mul_assoc] using hinner)
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hcoeff)

/-- A fixed choice of a nonzero vector for every Koopman eigenvalue. -/
noncomputable def koopmanEigenvector
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    Lp ℂ (2 : ℝ≥0∞) mu :=
  Classical.choose lambda.property

theorem koopmanEigenvector_ne_zero
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    koopmanEigenvector T mu hT lambda ≠ 0 :=
  (Classical.choose_spec lambda.property).1

theorem koopmanEigenvector_eigen
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    koopmanL2Complex T mu hT (koopmanEigenvector T mu hT lambda) =
      (lambda : ℂ) • koopmanEigenvector T mu hT lambda :=
  (Classical.choose_spec lambda.property).2

noncomputable def normalizedKoopmanEigenvector
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    Lp ℂ (2 : ℝ≥0∞) mu :=
  ((‖koopmanEigenvector T mu hT lambda‖⁻¹ : ℝ) : ℂ) •
    koopmanEigenvector T mu hT lambda

theorem norm_normalizedKoopmanEigenvector
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    ‖normalizedKoopmanEigenvector T mu hT lambda‖ = 1 := by
  rw [normalizedKoopmanEigenvector, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr
    (koopmanEigenvector_ne_zero T mu hT lambda))

theorem normalizedKoopmanEigenvector_eigen
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    koopmanL2Complex T mu hT
        (normalizedKoopmanEigenvector T mu hT lambda) =
      (lambda : ℂ) • normalizedKoopmanEigenvector T mu hT lambda := by
  simp only [normalizedKoopmanEigenvector, map_smul]
  rw [koopmanEigenvector_eigen]
  exact smul_comm _ _ _

theorem one_le_dist_normalizedKoopmanEigenvector
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    {lambda gamma : {z : ℂ // IsKoopmanEigenvalue T mu hT z}}
    (hne : lambda ≠ gamma) :
    1 ≤ dist (normalizedKoopmanEigenvector T mu hT lambda)
      (normalizedKoopmanEigenvector T mu hT gamma) := by
  have hval : (lambda : ℂ) ≠ gamma := fun h => hne (Subtype.ext h)
  have hinner : inner ℂ
      (normalizedKoopmanEigenvector T mu hT lambda)
      (normalizedKoopmanEigenvector T mu hT gamma) = 0 :=
    inner_eq_zero_of_koopman_eigenvectors T mu hT
      (by rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]; norm_num)
      (by rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]; norm_num)
      (normalizedKoopmanEigenvector_eigen T mu hT lambda)
      (normalizedKoopmanEigenvector_eigen T mu hT gamma) hval
  have hsquare : ‖normalizedKoopmanEigenvector T mu hT lambda -
        normalizedKoopmanEigenvector T mu hT gamma‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hinner, map_zero,
      norm_normalizedKoopmanEigenvector,
      norm_normalizedKoopmanEigenvector]
    norm_num
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (normalizedKoopmanEigenvector T mu hT lambda -
    normalizedKoopmanEigenvector T mu hT gamma)]

/-- The point spectrum of a Koopman operator on a standard compact metric
probability space is countable. -/
theorem countable_koopmanEigenvalues
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsFiniteMeasure mu]
    (hT : MeasurePreserving T mu mu) :
    Set.Countable {z : ℂ | IsKoopmanEigenvalue T mu hT z} := by
  let : MeasureTheory.IsSeparable mu := inferInstance
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℂ (2 : ℝ≥0∞) mu) := inferInstance
  let Lambda := {z : ℂ // IsKoopmanEigenvalue T mu hT z}
  let : TopologicalSpace Lambda := ⊥
  let : DiscreteTopology Lambda := ⟨rfl⟩
  let f : Lambda → Lp ℂ (2 : ℝ≥0∞) mu :=
    normalizedKoopmanEigenvector T mu hT
  have hf : IsClosedEmbedding f :=
    Metric.isClosedEmbedding_of_pairwise_le_dist (show (0 : ℝ) < 1 by norm_num)
      (fun _ _ hne => one_le_dist_normalizedKoopmanEigenvector T mu hT hne)
  have : TopologicalSpace.SeparableSpace Lambda := hf.isEmbedding.separableSpace
  have hcount : Countable Lambda :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact hcount

noncomputable instance instMeasurableSpaceCircle656 : MeasurableSpace Circle :=
  inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
instance instBorelSpaceCircle656 : BorelSpace Circle :=
  inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
noncomputable instance instMeasurableSpaceAdditiveCircle656 :
    MeasurableSpace (Additive Circle) :=
  inferInstanceAs (MeasurableSpace Circle)
instance instBorelSpaceAdditiveCircle656 : BorelSpace (Additive Circle) :=
  inferInstanceAs (BorelSpace Circle)

noncomputable def complexRadialCircle (z : {z : ℂ // z ≠ 0}) : Circle :=
  ⟨z / (‖(z : ℂ)‖ : ℂ), by
    change (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg (z : ℂ)), div_self]
    exact norm_ne_zero_iff.mpr z.property⟩

theorem measurable_complexRadialCircle : Measurable complexRadialCircle := by
  exact (by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div
      (Complex.continuous_ofReal.comp
        (continuous_norm.comp continuous_subtype_val))
      (fun z => Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr z.property)) : Continuous complexRadialCircle).measurable

theorem exists_measurable_complexToCircle :
    ∃ f : ℂ → Circle, Measurable f ∧
      ∀ z : {z : ℂ // z ≠ 0}, f z = complexRadialCircle z := by
  obtain ⟨f, hf, heq⟩ :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : ℂ)).compl).exists_measurable_extend
      measurable_complexRadialCircle (fun _ => inferInstance)
  exact ⟨f, hf, congr_fun heq⟩

noncomputable def complexToCircle : ℂ → Circle :=
  exists_measurable_complexToCircle.choose

theorem coe_complexToCircle_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    (complexToCircle z : ℂ) = z / (‖z‖ : ℂ) := by
  have h := exists_measurable_complexToCircle.choose_spec.2 ⟨z, hz⟩
  exact congrArg ((↑) : Circle → ℂ) h

theorem measurable_complexToCircle : Measurable complexToCircle := by
  exact exists_measurable_complexToCircle.choose_spec.1

theorem eigenvector_norm_ae_const'
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu) (herg : Ergodic T mu)
    {lambda : ℂ} {v : Lp ℂ (2 : ℝ≥0∞) mu}
    (hv0 : v ≠ 0)
    (hv : koopmanL2Complex T mu hT v = lambda • v) :
    ∃ c : ℝ, c ≠ 0 ∧ (fun x => ‖v x‖) =ᵐ[mu] (fun _ => c) := by
  have heigen : (fun x => v (T x)) =ᵐ[mu] (fun x => lambda * v x) := by
    have hcoe := Lp.ext_iff.mp hv
    filter_upwards [Lp.coeFn_compMeasurePreserving v hT,
      Lp.coeFn_smul lambda v, hcoe] with x hcomp hsmul heq
    exact hcomp.symm.trans (heq.trans hsmul)
  have hnormInv : (fun x => ‖v (T x)‖) =ᵐ[mu] (fun x => ‖v x‖) := by
    filter_upwards [heigen] with x hx
    rw [hx, norm_mul, norm_eq_one_of_isKoopmanEigenvalue T mu hT
      ⟨v, hv0, hv⟩]
    simp
  obtain ⟨c, hc⟩ := herg.ae_eq_const_of_ae_eq_comp_ae
    (Lp.aestronglyMeasurable v).norm (by simpa [Function.comp_def] using hnormInv)
  refine ⟨c, ?_, hc⟩
  intro hc0
  apply hv0
  rw [Lp.ext_iff]
  filter_upwards [hc, Lp.coeFn_zero ℂ (2 : ℝ≥0∞) mu] with x hx hz
  rw [hc0] at hx
  exact (norm_eq_zero.mp hx).trans hz.symm

theorem complexToCircle_mul_of_norm_left_eq_one
    {lambda z : ℂ} (hlambda : ‖lambda‖ = 1) (hz : z ≠ 0) :
    complexToCircle (lambda * z) =
      ⟨lambda, by
        change lambda ∈ Metric.sphere (0 : ℂ) 1
        simpa [mem_sphere_zero_iff_norm]⟩ * complexToCircle z := by
  apply Circle.ext
  change (complexToCircle (lambda * z) : ℂ) =
    lambda * (complexToCircle z : ℂ)
  rw [coe_complexToCircle_of_ne_zero (mul_ne_zero
      (norm_ne_zero_iff.mp (by rw [hlambda]; norm_num)) hz),
    coe_complexToCircle_of_ne_zero hz]
  rw [norm_mul, hlambda, one_mul]
  rw [mul_div_assoc]

noncomputable def koopmanEigenfunctionRepresentative
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) : X → ℂ :=
  let v := normalizedKoopmanEigenvector T mu hT lambda
  (Lp.aestronglyMeasurable v).mk v

theorem measurable_koopmanEigenfunctionRepresentative
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    Measurable (koopmanEigenfunctionRepresentative T mu hT lambda) := by
  exact (Lp.aestronglyMeasurable
    (normalizedKoopmanEigenvector T mu hT lambda)).measurable_mk

noncomputable def koopmanEigenfunctionCircle
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) (x : X) : Circle :=
  complexToCircle (koopmanEigenfunctionRepresentative T mu hT lambda x)

theorem measurable_koopmanEigenfunctionCircle
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    Measurable (koopmanEigenfunctionCircle T mu hT lambda) := by
  exact measurable_complexToCircle.comp
    (measurable_koopmanEigenfunctionRepresentative T mu hT lambda)

theorem koopmanEigenfunctionRepresentative_ae_eq
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    koopmanEigenfunctionRepresentative T mu hT lambda =ᵐ[mu]
      (normalizedKoopmanEigenvector T mu hT lambda : X → ℂ) := by
  exact (Lp.aestronglyMeasurable
    (normalizedKoopmanEigenvector T mu hT lambda)).ae_eq_mk.symm

theorem koopmanEigenfunctionRepresentative_ne_zero_ae
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu) (herg : Ergodic T mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    ∀ᵐ x ∂mu, koopmanEigenfunctionRepresentative T mu hT lambda x ≠ 0 := by
  let v := normalizedKoopmanEigenvector T mu hT lambda
  have hv0 : v ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]
    norm_num
  obtain ⟨c, hc0, hc⟩ := eigenvector_norm_ae_const' T mu hT herg hv0
    (normalizedKoopmanEigenvector_eigen T mu hT lambda)
  have hrep := koopmanEigenfunctionRepresentative_ae_eq T mu hT lambda
  filter_upwards [hc, hrep] with x hcx hrx
  intro hzero
  have hvx0 : v x = 0 := by
    exact hrx.symm.trans hzero
  rw [hvx0, norm_zero] at hcx
  exact hc0 hcx.symm

theorem koopmanEigenfunctionRepresentative_eigen_ae
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    (fun x => koopmanEigenfunctionRepresentative T mu hT lambda (T x)) =ᵐ[mu]
      (fun x => (lambda : ℂ) *
        koopmanEigenfunctionRepresentative T mu hT lambda x) := by
  let v := normalizedKoopmanEigenvector T mu hT lambda
  have hvLp := normalizedKoopmanEigenvector_eigen T mu hT lambda
  have hv : (fun x => v (T x)) =ᵐ[mu]
      (fun x => (lambda : ℂ) * v x) := by
    have hcoe := Lp.ext_iff.mp hvLp
    filter_upwards [Lp.coeFn_compMeasurePreserving v hT,
      Lp.coeFn_smul (lambda : ℂ) v, hcoe] with x hcomp hsmul heq
    exact hcomp.symm.trans (heq.trans hsmul)
  have hrep := koopmanEigenfunctionRepresentative_ae_eq T mu hT lambda
  have hrepT := hT.quasiMeasurePreserving.ae_eq_comp hrep
  filter_upwards [hv, hrep, hrepT] with x hx hrx hrTx
  exact hrTx.trans (hx.trans (congrArg ((lambda : ℂ) * ·) hrx.symm))

noncomputable def koopmanEigenvalueCircle
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) : Circle :=
  ⟨lambda, by
    change (lambda : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    simpa [mem_sphere_zero_iff_norm] using
      norm_eq_one_of_isKoopmanEigenvalue T mu hT lambda.property⟩

@[simp] theorem coe_koopmanEigenvalueCircle
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    (koopmanEigenvalueCircle T mu hT lambda : ℂ) = lambda := rfl

theorem koopmanEigenfunctionCircle_eigen_ae
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu) (herg : Ergodic T mu)
    (lambda : {z : ℂ // IsKoopmanEigenvalue T mu hT z}) :
    (fun x => koopmanEigenfunctionCircle T mu hT lambda (T x)) =ᵐ[mu]
      (fun x => koopmanEigenvalueCircle T mu hT lambda *
        koopmanEigenfunctionCircle T mu hT lambda x) := by
  filter_upwards [koopmanEigenfunctionRepresentative_eigen_ae T mu hT lambda,
    koopmanEigenfunctionRepresentative_ne_zero_ae T mu hT herg lambda]
    with x hx hne
  unfold koopmanEigenfunctionCircle
  rw [hx]
  exact complexToCircle_mul_of_norm_left_eq_one
    (norm_eq_one_of_isKoopmanEigenvalue T mu hT lambda.property) hne

abbrev KoopmanEigenvalueType
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :=
  {z : ℂ // IsKoopmanEigenvalue T mu hT z}

abbrev KroneckerAmbient
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :=
  KoopmanEigenvalueType T mu hT → Additive Circle

noncomputable def kroneckerAmbientMap
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :
    X → KroneckerAmbient T mu hT :=
  fun x lambda => Additive.ofMul
    (koopmanEigenfunctionCircle T mu hT lambda x)

theorem measurable_kroneckerAmbientMap
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :
    Measurable (kroneckerAmbientMap T mu hT) := by
  exact Measurable.of_eval fun lambda =>
    measurable_koopmanEigenfunctionCircle T mu hT lambda

noncomputable def kroneckerAmbientRotation
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :
    KroneckerAmbient T mu hT :=
  fun lambda => Additive.ofMul (koopmanEigenvalueCircle T mu hT lambda)

theorem kroneckerAmbientMap_eigen_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu) (herg : Ergodic T mu) :
    (fun x => kroneckerAmbientMap T mu hT (T x)) =ᵐ[mu]
      (fun x => kroneckerAmbientRotation T mu hT +
        kroneckerAmbientMap T mu hT x) := by
  let : Countable (KoopmanEigenvalueType T mu hT) :=
    (countable_koopmanEigenvalues T mu hT).to_subtype
  filter_upwards [ae_all_iff.2 fun lambda =>
    koopmanEigenfunctionCircle_eigen_ae T mu hT herg lambda]
    with x hx
  funext lambda
  exact hx lambda

theorem ergodic_map_of_ae_semiconj
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (T : X → X) (mu : Measure X) (hT : Ergodic T mu)
    (pi : X → Z) (hpi : Measurable pi) (R : Z → Z) (hR : Measurable R)
    (hcomm : pi ∘ T =ᵐ[mu] R ∘ pi) :
    Ergodic R (Measure.map pi mu) := by
  have hRpres : MeasurePreserving R (Measure.map pi mu) (Measure.map pi mu) := by
    refine ⟨hR, ?_⟩
    rw [Measure.map_map hR hpi, Measure.map_congr hcomm.symm,
      ← Measure.map_map hpi hT.measurable, hT.map_eq]
  refine ⟨hRpres, ?_⟩
  constructor
  intro s hs hRs
  have hpre : T ⁻¹' (pi ⁻¹' s) =ᵐ[mu] pi ⁻¹' s := by
    filter_upwards [hcomm] with x hx
    change (pi (T x) ∈ s) = (pi x ∈ s)
    apply propext
    change pi (T x) = R (pi x) at hx
    rw [hx]
    exact Set.ext_iff.mp hRs (pi x)
  have hc : EventuallyConst (pi ⁻¹' s) (ae mu) :=
    hT.quasiErgodic.aeconst_set₀
      (hs.preimage hpi).nullMeasurableSet hpre
  exact ((hpi.measurePreserving mu).aeconst_preimage hs.nullMeasurableSet).mp hc

noncomputable def kroneckerAmbientMeasure
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) :
    Measure (KroneckerAmbient T mu hT) :=
  Measure.map (kroneckerAmbientMap T mu hT) mu

instance instIsProbabilityMeasureKroneckerAmbientMeasure
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu) :
    IsProbabilityMeasure (kroneckerAmbientMeasure T mu hT) := by
  unfold kroneckerAmbientMeasure
  infer_instance

theorem ergodic_kroneckerAmbientRotation
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Ergodic
      (fun z : KroneckerAmbient T mu hT.toMeasurePreserving ↦
        kroneckerAmbientRotation T mu hT.toMeasurePreserving + z)
      (kroneckerAmbientMeasure T mu hT.toMeasurePreserving) := by
  let pi := kroneckerAmbientMap T mu hT.toMeasurePreserving
  let R := fun z : KroneckerAmbient T mu hT.toMeasurePreserving ↦
    kroneckerAmbientRotation T mu hT.toMeasurePreserving + z
  apply ergodic_map_of_ae_semiconj T mu hT pi
    (measurable_kroneckerAmbientMap T mu hT.toMeasurePreserving) R
  · exact measurable_const.add measurable_id
  · simpa [Function.comp_def, pi, R] using
      kroneckerAmbientMap_eigen_ae T mu hT.toMeasurePreserving hT

theorem mem_support_map_homeomorph_iff
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X]
    (e : X ≃ₜ X) (mu : Measure X) (x : X) :
    x ∈ (Measure.map e mu).support ↔ e.symm x ∈ mu.support := by
  simp only [Measure.support_eq_forall_isOpen, Set.mem_ofPred_eq]
  constructor
  · intro hx V hxV hV
    let U : Set X := e.symm ⁻¹' V
    have hU : IsOpen U := hV.preimage e.symm.continuous
    have hxU : x ∈ U := by simpa [U]
    have hpos := hx U hxU hU
    rw [Measure.map_apply e.measurable hU.measurableSet] at hpos
    have heq : e ⁻¹' U = V := by
      ext z
      simp [U]
    rwa [heq] at hpos
  · intro hx U hxU hU
    have hpreOpen : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
    have hpreMem : e.symm x ∈ e ⁻¹' U := by simpa
    rw [Measure.map_apply e.measurable hU.measurableSet]
    exact hx (e ⁻¹' U) hpreMem hpreOpen

theorem mem_topologicalClosure_zmultiples_sub_of_mem_support
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [OpensMeasurableSpace Z]
    [BorelSpace Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (mu : Measure Z) (alpha : Z)
    (hrot : Ergodic (fun z : Z ↦ alpha + z) mu)
    {x y : Z} (hx : x ∈ mu.support) (hy : y ∈ mu.support) :
    y - x ∈ (AddSubgroup.zmultiples alpha).topologicalClosure := by
  let e : Z ≃ₜ Z := Homeomorph.addLeft (-x)
  let nu : Measure Z := Measure.map e mu
  have hzero : (0 : Z) ∈ nu.support := by
    rw [mem_support_map_homeomorph_iff e mu]
    change -(-x) + 0 ∈ mu.support
    simpa using hx
  have hd : y - x ∈ nu.support := by
    rw [mem_support_map_homeomorph_iff e mu]
    change -(-x) + (y - x) ∈ mu.support
    convert hy using 1
    abel
  have hnuRot : Ergodic (fun z : Z ↦ alpha + z) nu := by
    apply ergodic_map_of_ae_semiconj (fun z : Z ↦ alpha + z) mu hrot e
      e.measurable (fun z : Z ↦ alpha + z)
      (measurable_const.add measurable_id)
    exact Filter.Eventually.of_forall fun z ↦ by
      change e (alpha + z) = alpha + e z
      simp only [e, Homeomorph.coe_addLeft]
      abel
  change y - x ∈ closure ((AddSubgroup.zmultiples alpha : AddSubgroup Z) : Set Z)
  rw [AddSubgroup.coe_zmultiples]
  by_contra hnot
  let orbit : Set Z := Set.range fun n : ℤ ↦ n • alpha
  have hnotmem : y - x ∈ (closure orbit)ᶜ := by
    exact hnot
  have hnotopen : IsOpen ((closure orbit)ᶜ) :=
    (isClosed_closure : IsClosed (closure orbit)).isOpen_compl
  have hnotnhds :=
    @IsOpen.mem_nhds Z _ (y - x) ((closure orbit)ᶜ) hnotopen hnotmem
  have hcont : Tendsto (fun p : Z × Z ↦ (y - x) + p.1 - p.2)
      (𝓝 ((0 : Z), (0 : Z))) (𝓝 (y - x)) := by
    have hf : Continuous (Prod.fst : Z × Z → Z) := continuous_fst
    have hs : Continuous (Prod.snd : Z × Z → Z) := continuous_snd
    have hc : Continuous (fun p : Z × Z ↦ (y - x) + p.1 - p.2) :=
      (continuous_const.add hf).sub hs
    exact hc.tendsto' ((0 : Z), (0 : Z)) (y - x) (by simp)
  have hrect : ∃ U W : Set Z,
      @IsOpen Z (inferInstance : TopologicalSpace Z) U ∧ 0 ∈ U ∧
      @IsOpen Z (inferInstance : TopologicalSpace Z) W ∧ 0 ∈ W ∧
        U ×ˢ W ⊆ (fun p : Z × Z ↦ (y - x) + p.1 - p.2) ⁻¹' (closure orbit)ᶜ :=
    (@mem_nhds_prod_iff' Z Z _ _ (0 : Z) (0 : Z) _).1 (hcont hnotnhds)
  rcases hrect with ⟨U, W, hUopen, hUzero, hWopen, hWzero, hUW⟩
  let V : Set Z := U ∩ W
  have hVzero : (0 : Z) ∈ V := ⟨hUzero, hWzero⟩
  have hVopen : IsOpen V := hUopen.inter hWopen
  have hVavoidClosure : ∀ u ∈ V, ∀ v ∈ V,
      (y - x) + u - v ∉ closure orbit := by
    intro u hu v hv
    exact hUW (show (u, v) ∈ U ×ˢ W from ⟨hu.1, hv.2⟩)
  have hVavoid : ∀ u ∈ V, ∀ v ∈ V, ∀ n : ℤ,
      n • alpha ≠ (y - x) + u - v := by
    intro u hu v hv n heq
    apply hVavoidClosure u hu v hv
    rw [← heq]
    exact subset_closure ⟨n, rfl⟩
  let s : Set Z := ⋃ n : ℤ, n • alpha +ᵥ V
  have hsopen : IsOpen s := isOpen_iUnion fun n ↦ hVopen.vadd _
  have hszero : (0 : Z) ∈ s := by
    refine mem_iUnion.2 ⟨0, ?_⟩
    simpa using hVzero
  have hdisj : Disjoint s ((y - x) +ᵥ V) := by
    simp_rw [s, disjoint_iUnion_left, disjoint_left]
    intro n z hz hv
    rcases hz with ⟨u, hu, rfl⟩
    rcases hv with ⟨v, hv, huv⟩
    apply hVavoid v hv u hu n
    dsimp at huv ⊢
    rw [huv]
    abel
  have hsInv : (fun z : Z ↦ alpha + z) ⁻¹' s = s := by
    simp only [s, preimage_iUnion]
    refine iUnion_congr_of_surjective _ (add_left_surjective (-1)) fun n ↦ ?_
    ext z
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
    constructor <;> intro hz
    · simpa [add_zsmul, add_assoc] using hz
    · simpa [add_zsmul, add_assoc] using hz
  cases hnuRot.measure_self_or_compl_eq_zero hsopen.measurableSet hsInv with
  | inl hs0 =>
      exact ((Measure.mem_support_iff_forall (μ := nu) 0).1 hzero s
        (hsopen.mem_nhds hszero)).ne' hs0
  | inr hsc0 =>
      have htargetOpen : IsOpen ((y - x) +ᵥ V) := hVopen.vadd _
      have htargetMem : y - x ∈ (y - x) +ᵥ V := by
        exact ⟨0, hVzero, by simp⟩
      have htargetPos : 0 < nu ((y - x) +ᵥ V) :=
        (Measure.mem_support_iff_forall (μ := nu) (y - x)).1 hd _
          (htargetOpen.mem_nhds htargetMem)
      exact htargetPos.ne' (measure_mono_null
        (show (y - x) +ᵥ V ⊆ sᶜ from hdisj.subset_compl_left) hsc0)

theorem add_mem_support_iff_sub_mem_support
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [OpensMeasurableSpace Z]
    [BorelSpace Z]
    (mu : Measure Z) (alpha y : Z)
    (hpres : MeasurePreserving (fun z : Z ↦ alpha + z) mu mu) :
    y ∈ mu.support ↔ -alpha + y ∈ mu.support := by
  let e : Z ≃ₜ Z := Homeomorph.addLeft alpha
  have heq : Measure.map e mu = mu := by
    simpa only [e, Homeomorph.coe_addLeft] using hpres.map_eq
  calc
    y ∈ mu.support ↔ y ∈ (Measure.map e mu).support := by rw [heq]
    _ ↔ e.symm y ∈ mu.support := mem_support_map_homeomorph_iff e mu y
    _ ↔ -alpha + y ∈ mu.support := by rfl

theorem zsmul_add_mem_support
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [OpensMeasurableSpace Z]
    [BorelSpace Z]
    (mu : Measure Z) (alpha x : Z)
    (hpres : MeasurePreserving (fun z : Z ↦ alpha + z) mu mu)
    (hx : x ∈ mu.support) (n : ℤ) :
    n • alpha + x ∈ mu.support := by
  induction n using Int.induction_on with
  | zero => simpa using hx
  | @succ n ih =>
      have hfwd : alpha + ((n : ℤ) • alpha + x) ∈ mu.support := by
        rw [add_mem_support_iff_sub_mem_support mu alpha]
        · convert ih using 1
          abel
        · exact hpres
      convert hfwd using 1
      simp [add_zsmul]
      abel
  | @pred n ih =>
      have ih' : -((n : ℤ) • alpha) + x ∈ mu.support := by
        simpa using ih
      have hbwd : -alpha + (-((n : ℤ) • alpha) + x) ∈ mu.support :=
        (add_mem_support_iff_sub_mem_support mu alpha
          (-((n : ℤ) • alpha) + x) hpres).mp ih'
      convert hbwd using 1
      module

theorem support_eq_vadd_topologicalClosure_zmultiples
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [OpensMeasurableSpace Z]
    [BorelSpace Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (mu : Measure Z) (alpha z0 : Z)
    (hrot : Ergodic (fun z : Z ↦ alpha + z) mu)
    (hz0 : z0 ∈ mu.support) :
    mu.support = z0 +ᵥ ((AddSubgroup.zmultiples alpha).topologicalClosure : Set Z) := by
  ext y
  constructor
  · intro hy
    exact ⟨y - z0,
      mem_topologicalClosure_zmultiples_sub_of_mem_support mu alpha hrot hz0 hy,
      by simp [vadd_eq_add]⟩
  · rintro ⟨h, hh, rfl⟩
    rw [AddSubgroup.topologicalClosure_coe] at hh
    let S : Set Z := {q | z0 + q ∈ mu.support}
    have hSclosed : IsClosed S :=
      (Measure.isClosed_support : IsClosed mu.support).preimage
        (continuous_const.add continuous_id)
    apply (hSclosed.closure_subset_iff.2 ?_) hh
    intro q hq
    rcases hq with ⟨n, rfl⟩
    simpa [S, add_comm] using
      zsmul_add_mem_support mu alpha z0 hrot.toMeasurePreserving hz0 n

noncomputable def addTranslateProbability
    {Z : Type*} [MeasurableSpace Z] [Add Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m] (q : Z) : ProbabilityMeasure Z :=
  ⟨Measure.map (fun z : Z ↦ q + z) m, inferInstance⟩

@[simp] theorem addTranslateProbability_coe
    {Z : Type*} [MeasurableSpace Z] [Add Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m] (q : Z) :
    (addTranslateProbability m q : Measure Z) =
      Measure.map (fun z : Z ↦ q + z) m := rfl

theorem continuous_addTranslateProbability
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [BorelSpace Z]
    [MeasurableAdd₂ Z] [CompactSpace Z] [FirstCountableTopology Z]
    [SecondCountableTopology Z]
    (m : Measure Z) [IsProbabilityMeasure m] :
    Continuous (addTranslateProbability m) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  have hparam : Continuous (fun p : Z × Z ↦ f (p.1 + p.2)) := by
    fun_prop
  have hcont : Continuous (fun q : Z ↦ ∫ z, f (q + z) ∂m) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := m) hparam (s := (Set.univ : Set Z)) isCompact_univ)
  convert hcont using 1
  funext q
  rw [addTranslateProbability_coe]
  exact integral_map (measurable_const.add measurable_id).aemeasurable
    f.continuous.aestronglyMeasurable

theorem isClosed_addTranslateStabilizer
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [BorelSpace Z]
    [MeasurableAdd₂ Z] [CompactSpace Z] [FirstCountableTopology Z]
    [SecondCountableTopology Z]
    (m : Measure Z) [IsProbabilityMeasure m] :
    IsClosed {q : Z | Measure.map (fun z : Z ↦ q + z) m = m} := by
  let pm : ProbabilityMeasure Z := ⟨m, inferInstance⟩
  have hclosed : IsClosed {q : Z | addTranslateProbability m q = pm} :=
    isClosed_eq (continuous_addTranslateProbability m) continuous_const
  have heq : {q : Z | Measure.map (fun z : Z ↦ q + z) m = m} =
      {q : Z | addTranslateProbability m q = pm} := by
    ext q
    change Measure.map (fun z : Z ↦ q + z) m = m ↔
      addTranslateProbability m q = pm
    constructor
    · intro h
      apply ProbabilityMeasure.toMeasure_injective
      exact h
    · intro h
      exact congrArg ProbabilityMeasure.toMeasure h
  rw [heq]
  exact hclosed

theorem map_add_left_zsmul_eq_self
    {Z : Type*} [MeasurableSpace Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) (alpha : Z)
    (hpres : MeasurePreserving (fun z : Z ↦ alpha + z) m m)
    (n : ℤ) :
    Measure.map (fun z : Z ↦ n • alpha + z) m = m := by
  have hiterate (a : Z) (ha : MeasurePreserving (fun z : Z ↦ a + z) m m)
      (k : ℕ) : Measure.map (fun z : Z ↦ (k : ℤ) • a + z) m = m := by
    have hformula : (fun z : Z ↦ a + z)^[k] =
        (fun z : Z ↦ (k : ℤ) • a + z) := by
      induction k with
      | zero => funext z; simp
      | succ k ih =>
          funext z
          rw [Function.iterate_succ_apply, ih]
          simp only [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
          abel
    rw [← hformula]
    exact (ha.iterate k).map_eq
  cases n with
  | ofNat k => exact hiterate alpha hpres k
  | negSucc k =>
      have hneg : Measure.map (fun z : Z ↦ -alpha + z) m = m := by
        calc
          Measure.map (fun z : Z ↦ -alpha + z) m =
              Measure.map (fun z : Z ↦ -alpha + z)
                (Measure.map (fun z : Z ↦ alpha + z) m) := by rw [hpres.map_eq]
          _ = Measure.map ((fun z : Z ↦ -alpha + z) ∘
                (fun z : Z ↦ alpha + z)) m :=
            Measure.map_map (measurable_const.add measurable_id)
              (measurable_const.add measurable_id)
          _ = Measure.map id m := by
            congr 1
            funext z
            simp
          _ = m := Measure.map_id
      have hnegPres : MeasurePreserving (fun z : Z ↦ -alpha + z) m m :=
        ⟨measurable_const.add measurable_id, hneg⟩
      have hi := hiterate (-alpha) hnegPres (k + 1)
      convert hi using 1
      congr 1
      funext z
      rw [Int.negSucc_eq]
      push_cast
      simp only [neg_smul, smul_neg]

theorem isAddLeftInvariant_of_dense_zmultiples
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [BorelSpace Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [CompactSpace Z] [FirstCountableTopology Z]
    [SecondCountableTopology Z]
    (m : Measure Z) [IsProbabilityMeasure m] (alpha : Z)
    (hpres : MeasurePreserving (fun z : Z ↦ alpha + z) m m)
    (hdense : DenseRange (fun n : ℤ ↦ n • alpha)) :
    Measure.IsAddLeftInvariant m := by
  constructor
  intro q
  let S : Set Z := {r : Z | Measure.map (fun z : Z ↦ r + z) m = m}
  have hSclosed : IsClosed S := isClosed_addTranslateStabilizer m
  have hrange : Set.range (fun n : ℤ ↦ n • alpha) ⊆ S := by
    rintro _ ⟨n, rfl⟩
    exact map_add_left_zsmul_eq_self m alpha hpres n
  have hclosure : closure (Set.range (fun n : ℤ ↦ n • alpha)) ⊆ S :=
    closure_minimal hrange hSclosed
  exact hclosure (hdense.closure_eq.symm ▸ mem_univ q)

theorem isAddHaarMeasure_of_dense_rotation
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [BorelSpace Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [CompactSpace Z] [FirstCountableTopology Z]
    [SecondCountableTopology Z]
    (m : Measure Z) [IsProbabilityMeasure m] (alpha : Z)
    (hpres : MeasurePreserving (fun z : Z ↦ alpha + z) m m)
    (hdense : DenseRange (fun n : ℤ ↦ n • alpha)) :
    Measure.IsAddHaarMeasure m := by
  let : Measure.IsAddLeftInvariant m :=
    isAddLeftInvariant_of_dense_zmultiples m alpha hpres hdense
  exact Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
    m Set.univ isCompact_univ (by simp) (by simp) (by simp)

noncomputable abbrev KroneckerSubgroup
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu) : AddSubgroup
      (KroneckerAmbient T mu hT) :=
  (AddSubgroup.zmultiples (kroneckerAmbientRotation T mu hT)).topologicalClosure

noncomputable def kroneckerAmbientBasepoint
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    KroneckerAmbient T mu hT.toMeasurePreserving := by
  letI : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  exact Classical.choose (Measure.nonempty_support
    (μ := kroneckerAmbientMeasure T mu hT.toMeasurePreserving) (by
    rw [← Measure.measure_univ_ne_zero]
    simp))

theorem kroneckerAmbientBasepoint_mem_support
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    kroneckerAmbientBasepoint T mu hT ∈
      (kroneckerAmbientMeasure T mu hT.toMeasurePreserving).support := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  exact Classical.choose_spec (Measure.nonempty_support
    (μ := kroneckerAmbientMeasure T mu hT.toMeasurePreserving) (by
    rw [← Measure.measure_univ_ne_zero]
    simp))

noncomputable def kroneckerFactorMap
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    X → KroneckerSubgroup T mu hT.toMeasurePreserving := by
  classical
  exact fun x ↦
    if hx : kroneckerAmbientMap T mu hT.toMeasurePreserving x -
        kroneckerAmbientBasepoint T mu hT ∈
          KroneckerSubgroup T mu hT.toMeasurePreserving then
      ⟨kroneckerAmbientMap T mu hT.toMeasurePreserving x -
        kroneckerAmbientBasepoint T mu hT, hx⟩
    else 0

theorem measurable_kroneckerFactorMap
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : Measurable (kroneckerFactorMap T mu hT) := by
  classical
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let Z := KroneckerAmbient T mu hT.toMeasurePreserving
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let f : X → Z := fun x ↦ kroneckerAmbientMap T mu hT.toMeasurePreserving x -
    kroneckerAmbientBasepoint T mu hT
  have hf : Measurable f :=
    (measurable_kroneckerAmbientMap T mu hT.toMeasurePreserving).sub measurable_const
  have hH : MeasurableSet (H : Set Z) :=
    (AddSubgroup.isClosed_topologicalClosure _).measurableSet
  let s : Set X := {x | f x ∈ H}
  have hs : MeasurableSet s := hf hH
  have hyes : Measurable (fun x : s ↦
      (⟨f x, x.property⟩ : H)) :=
    Measurable.subtype_mk (hf.comp measurable_subtype_coe)
  have hno : Measurable (fun _ : (sᶜ : Set X) ↦ (0 : H)) := measurable_const
  let g : X → H := fun x ↦
    if hx : x ∈ s then ⟨f x, hx⟩ else 0
  have hg : Measurable g := Measurable.dite hyes hno hs
  have heq : kroneckerFactorMap T mu hT = g := by
    funext x
    apply Subtype.ext
    simp [kroneckerFactorMap, g, s, f, H]
  rw [heq]
  exact hg

theorem kroneckerFactorMap_coe_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    (fun x ↦ ((kroneckerFactorMap T mu hT x :
      KroneckerSubgroup T mu hT.toMeasurePreserving) :
        KroneckerAmbient T mu hT.toMeasurePreserving)) =ᵐ[mu]
      (fun x ↦ kroneckerAmbientMap T mu hT.toMeasurePreserving x -
        kroneckerAmbientBasepoint T mu hT) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let Z := KroneckerAmbient T mu hT.toMeasurePreserving
  let alpha := kroneckerAmbientRotation T mu hT.toMeasurePreserving
  let z0 := kroneckerAmbientBasepoint T mu hT
  let nu := kroneckerAmbientMeasure T mu hT.toMeasurePreserving
  have hsupport : ∀ᵐ z ∂nu, z ∈ nu.support := Measure.support_mem_ae
  have hpre : ∀ᵐ x ∂mu,
      kroneckerAmbientMap T mu hT.toMeasurePreserving x ∈ nu.support :=
    ae_of_ae_map
      (measurable_kroneckerAmbientMap T mu hT.toMeasurePreserving).aemeasurable
      hsupport
  have hsuppEq : nu.support = z0 +ᵥ
      ((KroneckerSubgroup T mu hT.toMeasurePreserving :
        AddSubgroup Z) : Set Z) := by
    exact support_eq_vadd_topologicalClosure_zmultiples nu alpha z0
      (ergodic_kroneckerAmbientRotation T mu hT)
      (kroneckerAmbientBasepoint_mem_support T mu hT)
  filter_upwards [hpre] with x hx
  have hmem : kroneckerAmbientMap T mu hT.toMeasurePreserving x - z0 ∈
      KroneckerSubgroup T mu hT.toMeasurePreserving := by
    rw [hsuppEq] at hx
    rcases hx with ⟨q, hq, heq⟩
    have : kroneckerAmbientMap T mu hT.toMeasurePreserving x - z0 = q := by
      rw [← heq]
      simp [vadd_eq_add]
    rwa [this]
  change kroneckerAmbientMap T mu hT.toMeasurePreserving x -
      kroneckerAmbientBasepoint T mu hT ∈
        KroneckerSubgroup T mu hT.toMeasurePreserving at hmem
  rw [kroneckerFactorMap, dite_eq_left hmem]

noncomputable def kroneckerSubgroupRotation
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : KroneckerSubgroup T mu hT.toMeasurePreserving :=
  ⟨kroneckerAmbientRotation T mu hT.toMeasurePreserving,
    (AddSubgroup.zmultiples _).le_topologicalClosure
      (AddSubgroup.mem_zmultiples _)⟩

theorem denseRange_zsmul_kroneckerSubgroupRotation
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    DenseRange (fun n : ℤ ↦ n • kroneckerSubgroupRotation T mu hT) := by
  let alpha := kroneckerAmbientRotation T mu hT.toMeasurePreserving
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let f : ℤ → H := fun n ↦ ⟨n • alpha, by
    exact (AddSubgroup.zmultiples alpha).le_topologicalClosure
      (AddSubgroup.zsmul_mem_zmultiples alpha n)⟩
  change DenseRange f
  intro z
  rw [closure_subtype]
  have himage : ((↑) : H → KroneckerAmbient T mu hT.toMeasurePreserving) ''
      Set.range f = Set.range (fun n : ℤ ↦ n • alpha) := by
    ext q
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨f n, ⟨n, rfl⟩, rfl⟩
  rw [himage]
  exact z.2

theorem kroneckerFactorMap_semiconj_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    (fun x ↦ kroneckerFactorMap T mu hT (T x)) =ᵐ[mu]
      (fun x ↦ kroneckerSubgroupRotation T mu hT +
        kroneckerFactorMap T mu hT x) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  have hcoe := kroneckerFactorMap_coe_ae T mu hT
  have hcoeT := hT.quasiMeasurePreserving.ae_eq_comp hcoe
  filter_upwards [kroneckerAmbientMap_eigen_ae T mu hT.toMeasurePreserving hT,
    hcoe, hcoeT] with x heigen hx hTx
  change ((kroneckerFactorMap T mu hT (T x) :
      KroneckerSubgroup T mu hT.toMeasurePreserving) :
        KroneckerAmbient T mu hT.toMeasurePreserving) =
    kroneckerAmbientMap T mu hT.toMeasurePreserving (T x) -
      kroneckerAmbientBasepoint T mu hT at hTx
  apply Subtype.ext
  rw [hTx, heigen]
  change kroneckerAmbientRotation T mu hT.toMeasurePreserving +
      kroneckerAmbientMap T mu hT.toMeasurePreserving x -
        kroneckerAmbientBasepoint T mu hT =
    kroneckerAmbientRotation T mu hT.toMeasurePreserving +
      ((kroneckerFactorMap T mu hT x :
        KroneckerSubgroup T mu hT.toMeasurePreserving) :
          KroneckerAmbient T mu hT.toMeasurePreserving)
  rw [hx]
  abel

noncomputable def kroneckerFactorMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : Measure (KroneckerSubgroup T mu hT.toMeasurePreserving) :=
  Measure.map (kroneckerFactorMap T mu hT) mu

instance instIsProbabilityMeasureKroneckerFactorMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : IsProbabilityMeasure (kroneckerFactorMeasure T mu hT) := by
  unfold kroneckerFactorMeasure
  infer_instance

theorem ergodic_kroneckerSubgroupRotation
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Ergodic (fun z ↦ kroneckerSubgroupRotation T mu hT + z)
      (kroneckerFactorMeasure T mu hT) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : BorelSpace H := inferInstance
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : MeasurableAdd₂ H := ContinuousAdd.measurableMul₂
  apply ergodic_map_of_ae_semiconj T mu hT
    (kroneckerFactorMap T mu hT) (measurable_kroneckerFactorMap T mu hT)
    (fun z ↦ kroneckerSubgroupRotation T mu hT + z)
    (measurable_const.add measurable_id)
  simpa [Function.comp_def] using kroneckerFactorMap_semiconj_ae T mu hT

theorem isAddHaarMeasure_kroneckerFactorMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Measure.IsAddHaarMeasure (kroneckerFactorMeasure T mu hT) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let : BorelSpace H := inferInstance
  let : MeasurableAdd₂ H := ContinuousAdd.measurableMul₂
  let : MeasurableNeg H := inferInstance
  exact isAddHaarMeasure_of_dense_rotation
    (kroneckerFactorMeasure T mu hT) (kroneckerSubgroupRotation T mu hT)
    (ergodic_kroneckerSubgroupRotation T mu hT).toMeasurePreserving
    (denseRange_zsmul_kroneckerSubgroupRotation T mu hT)

noncomputable def kroneckerFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Kernel (KroneckerSubgroup T mu hT.toMeasurePreserving) X :=
  condDistrib id (kroneckerFactorMap T mu hT) mu

instance instIsMarkovKernelKroneckerFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : IsMarkovKernel (kroneckerFiberKernel T mu hT) := by
  unfold kroneckerFiberKernel
  infer_instance

theorem bind_kroneckerFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Measure.bind (kroneckerFactorMeasure T mu hT)
      (kroneckerFiberKernel T mu hT) = mu := by
  have h := condDistrib_comp_map
    (μ := mu) (X := kroneckerFactorMap T mu hT) (Y := id)
    (measurable_kroneckerFactorMap T mu hT).aemeasurable aemeasurable_id
  simpa only [kroneckerFiberKernel, kroneckerFactorMeasure,
    Measure.map_id] using h

theorem kroneckerFiberKernel_fiber
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    ∀ᵐ z ∂kroneckerFactorMeasure T mu hT,
      ∀ᵐ x ∂kroneckerFiberKernel T mu hT z,
        kroneckerFactorMap T mu hT x = z := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : BorelSpace H := inferInstance
  let : MeasurableEq H := inferInstance
  let pi := kroneckerFactorMap T mu hT
  let eta := kroneckerFiberKernel T mu hT
  let m := kroneckerFactorMeasure T mu hT
  have hgraph : ∀ᵐ p ∂mu.map (fun x ↦ (pi x, id x)), pi p.2 = p.1 := by
    have hmeas : Measurable (fun x ↦ (pi x, id x)) :=
      (measurable_kroneckerFactorMap T mu hT).prodMk measurable_id
    have hset : MeasurableSet {p :
        KroneckerSubgroup T mu hT.toMeasurePreserving × X | pi p.2 = p.1} :=
      measurableSet_eq_fun ((measurable_kroneckerFactorMap T mu hT).comp measurable_snd)
        measurable_fst
    rw [ae_map_iff hmeas.aemeasurable hset]
    exact Filter.Eventually.of_forall fun x ↦ rfl
  have hjoint : m ⊗ₘ eta = mu.map (fun x ↦ (pi x, id x)) := by
    simpa only [m, eta, pi, kroneckerFactorMeasure, kroneckerFiberKernel] using
      (compProd_map_condDistrib (μ := mu) (X := kroneckerFactorMap T mu hT)
        (Y := id) (measurable_kroneckerFactorMap T mu hT).aemeasurable aemeasurable_id)
  have hgraph' : ∀ᵐ p ∂m ⊗ₘ eta, pi p.2 = p.1 := by
    rw [hjoint]
    exact hgraph
  exact Measure.ae_ae_of_ae_compProd hgraph'

abbrev KroneckerGraphSpace
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :=
  X × KroneckerSubgroup T mu hT.toMeasurePreserving

noncomputable def kroneckerGraphMap
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : X → KroneckerGraphSpace T mu hT :=
  fun x ↦ (x, kroneckerFactorMap T mu hT x)

theorem measurable_kroneckerGraphMap
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : Measurable (kroneckerGraphMap T mu hT) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  exact measurable_id.prodMk (measurable_kroneckerFactorMap T mu hT)

noncomputable def kroneckerGraphMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : Measure (KroneckerGraphSpace T mu hT) :=
  Measure.map (kroneckerGraphMap T mu hT) mu

instance instIsProbabilityMeasureKroneckerGraphMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : IsProbabilityMeasure (kroneckerGraphMeasure T mu hT) := by
  unfold kroneckerGraphMeasure
  infer_instance

noncomputable def kroneckerGraphTransform
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    KroneckerGraphSpace T mu hT → KroneckerGraphSpace T mu hT :=
  fun p ↦ (T p.1, kroneckerSubgroupRotation T mu hT + p.2)

theorem measurable_kroneckerGraphTransform
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Measurable (kroneckerGraphTransform T mu hT) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : BorelSpace H := inferInstance
  let : MeasurableAdd₂
      (KroneckerSubgroup T mu hT.toMeasurePreserving) :=
    ContinuousAdd.measurableMul₂
  exact (hT.measurable.comp measurable_fst).prodMk
    (measurable_const.add measurable_snd)

theorem continuous_kroneckerGraphTransform
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) (hTc : Continuous T) :
    Continuous (kroneckerGraphTransform T mu hT) := by
  exact (hTc.comp continuous_fst).prodMk (continuous_const.add continuous_snd)

theorem kroneckerGraphMap_semiconj_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    kroneckerGraphMap T mu hT ∘ T =ᵐ[mu]
      kroneckerGraphTransform T mu hT ∘ kroneckerGraphMap T mu hT := by
  filter_upwards [kroneckerFactorMap_semiconj_ae T mu hT] with x hx
  exact Prod.ext rfl hx

theorem ergodic_kroneckerGraphTransform
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Ergodic (kroneckerGraphTransform T mu hT)
      (kroneckerGraphMeasure T mu hT) := by
  exact ergodic_map_of_ae_semiconj T mu hT
    (kroneckerGraphMap T mu hT) (measurable_kroneckerGraphMap T mu hT)
    (kroneckerGraphTransform T mu hT)
    (measurable_kroneckerGraphTransform T mu hT)
    (kroneckerGraphMap_semiconj_ae T mu hT)

theorem map_fst_kroneckerGraphMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Measure.map Prod.fst (kroneckerGraphMeasure T mu hT) = mu := by
  rw [kroneckerGraphMeasure,
    Measure.map_map measurable_fst (measurable_kroneckerGraphMap T mu hT)]
  change Measure.map id mu = mu
  exact Measure.map_id

theorem map_snd_kroneckerGraphMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Measure.map Prod.snd (kroneckerGraphMeasure T mu hT) =
      kroneckerFactorMeasure T mu hT := by
  rw [kroneckerGraphMeasure, kroneckerFactorMeasure,
    Measure.map_map measurable_snd (measurable_kroneckerGraphMap T mu hT)]
  rfl

/-- A product system with a compact group rotation has the expected
iterate formula. -/
@[simp] theorem kroneckerGraphTransform_iterate_apply
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) (n : ℕ) (p : KroneckerGraphSpace T mu hT) :
    (kroneckerGraphTransform T mu hT)^[n] p =
      (T^[n] p.1, n • kroneckerSubgroupRotation T mu hT + p.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change (T (T^[n] p.1),
        kroneckerSubgroupRotation T mu hT +
          (n • kroneckerSubgroupRotation T mu hT + p.2)) = _
      simp only [Function.iterate_succ_apply', succ_nsmul]
      congr 1
      abel

/-- A support point of the graph measure projects to a support point of
the original measure. -/
theorem fst_mem_support_of_mem_support_kroneckerGraphMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) {q : KroneckerGraphSpace T mu hT}
    (hq : q ∈ (kroneckerGraphMeasure T mu hT).support) :
    q.1 ∈ mu.support := by
  rw [Measure.mem_support_iff_forall] at hq ⊢
  intro U hU
  obtain ⟨V, hVU, hVopen, hqV⟩ := mem_nhds_iff.mp hU
  have hpre : Prod.fst ⁻¹' V ∈ 𝓝 q :=
    (hVopen.preimage continuous_fst).mem_nhds hqV
  have hpos : 0 < kroneckerGraphMeasure T mu hT (Prod.fst ⁻¹' V) :=
    hq _ hpre
  have hmap : Measure.map Prod.fst (kroneckerGraphMeasure T mu hT) V =
      kroneckerGraphMeasure T mu hT (Prod.fst ⁻¹' V) :=
    Measure.map_apply measurable_fst hVopen.measurableSet
  have hVpos : 0 < mu V := by
    rw [← map_fst_kroneckerGraphMeasure T mu hT, hmap]
    exact hpos
  exact hVpos.trans_le (measure_mono hVU)

/-- If the first coordinate has a support-generic pointed orbit, then one
can choose a phase in the compact group so that the resulting product orbit
accumulates on any prescribed support point of the graph measure. -/
theorem exists_phase_graph_orbit_cluster
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) (a : X)
    (ha : IsSupportGeneric (fun n ↦ T^[n] a) mu)
    {q : KroneckerGraphSpace T mu hT}
    (hq : q ∈ (kroneckerGraphMeasure T mu hT).support) :
    ∃ z : KroneckerSubgroup T mu hT.toMeasurePreserving,
      MapClusterPt q atTop
        (fun n : ℕ ↦ (kroneckerGraphTransform T mu hT)^[n] (a, z)) := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (AddSubgroup.isClosed_topologicalClosure _).isCompact
  have hqfst : q.1 ∈ mu.support :=
    fst_mem_support_of_mem_support_kroneckerGraphMeasure T mu hT hq
  obtain ⟨n, hnmono, hnlim⟩ := (ha q.1 hqfst).tendsto_subseq
  let alpha : H := kroneckerSubgroupRotation T mu hT
  obtain ⟨z, sub, hsubmono, hsub⟩ :=
    CompactSpace.tendsto_subseq (fun k ↦ q.2 - n k • alpha)
  refine ⟨z, ?_⟩
  have hfirst : Tendsto (fun k ↦ T^[n (sub k)] a) atTop (𝓝 q.1) := by
    change Tendsto (((fun m : ℕ ↦ T^[m] a) ∘ n) ∘ sub) atTop (nhds q.1)
    exact hnlim.comp hsubmono.tendsto_atTop
  have hdelta : Tendsto
      (fun k ↦ q.2 + (z - (q.2 - n (sub k) • alpha))) atTop
      (𝓝 q.2) := by
    have hsub' : Tendsto (fun k ↦ q.2 - n (sub k) • alpha) atTop (nhds z) := by
      change Tendsto ((fun k ↦ q.2 - n k • alpha) ∘ sub) atTop (nhds z)
      exact hsub
    have hq : Tendsto (fun _ : ℕ ↦ q.2) atTop (nhds q.2) := tendsto_const_nhds
    have hz : Tendsto (fun _ : ℕ ↦ z) atTop (nhds z) := tendsto_const_nhds
    have h := hq.add (hz.sub hsub')
    simpa only [sub_self, add_zero] using h
  have hsecond : Tendsto (fun k ↦ n (sub k) • alpha + z)
      atTop (𝓝 q.2) := by
    convert hdelta using 1
    funext k
    abel
  have hprod := hfirst.prodMk_nhds hsecond
  have hlim : Tendsto
      ((fun m : ℕ ↦ (kroneckerGraphTransform T mu hT)^[m] (a, z)) ∘
        (n ∘ sub)) atTop (nhds q) := by
    change Tendsto
      (fun k ↦ (kroneckerGraphTransform T mu hT)^[n (sub k)] (a, z))
      atTop (nhds q)
    simpa only [Function.comp_apply, kroneckerGraphTransform_iterate_apply,
      alpha] using hprod
  exact hlim.mapClusterPt.of_comp (hnmono.comp hsubmono).tendsto_atTop

/-- Genericity can be transferred from an orbit-cluster point to the
original point by choosing, for each long prefix, an orbit start which
shadows that cluster point for the finitely many tests used so far. -/
theorem exists_genericAlongOrbitIntervals_of_orbit_cluster
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X]
    [CompactSpace X] [BorelSpace X] [SecondCountableTopology X]
    (S : X → X) (hS : Continuous S) (p q : X)
    (nu : Measure X) [IsProbabilityMeasure nu]
    (hcluster : MapClusterPt q atTop (fun n : ℕ ↦ S^[n] p))
    (length : ℕ → ℕ) (hlength : Tendsto length atTop atTop)
    (hqgeneric : ∀ f : BoundedContinuousFunction X ℝ,
      Tendsto (fun k ↦ birkhoffAverage ℝ S f (length k) q) atTop
        (nhds (∫ x, f x ∂nu))) :
    ∃ start : ℕ → ℕ,
      IsGenericAlongOrbitIntervals S p nu start length := by
  let : PseudoMetricSpace X :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  let : Nonempty X := ⟨p⟩
  let : TopologicalSpace.SeparableSpace
      (BoundedContinuousFunction X ℝ) := by
    let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
    exact e.surjective.denseRange.separableSpace e.continuous
  obtain ⟨G, hG⟩ := TopologicalSpace.exists_dense_seq
      (BoundedContinuousFunction X ℝ)
  let W : ℕ → Set X := fun k ↦
    ⋂ j ∈ Finset.range (k + 1),
      {x | dist
        (birkhoffAverage ℝ S (G j) (length k) x)
        (birkhoffAverage ℝ S (G j) (length k) q) <
          (1 : ℝ) / (k + 1)}
  have hWnhds (k : ℕ) : W k ∈ 𝓝 q := by
    apply IsOpen.mem_nhds
    · dsimp only [W]
      apply isOpen_biInter_finset
      intro j hj
      apply isOpen_lt
      · exact (continuous_birkhoffAverage_of_continuous S hS
          (G j) (G j).continuous (length k)).dist continuous_const
      · fun_prop
    · simp only [W, Set.mem_iInter, Set.mem_ofPred_eq]
      intro j
      simp only [Finset.mem_range]
      intro hj
      simp only [dist_self]
      positivity
  have hstartExists (k : ℕ) : ∃ s : ℕ, S^[s] p ∈ W k :=
    (mapClusterPt_iff_frequently.mp hcluster (W k) (hWnhds k)).exists
  let start : ℕ → ℕ := fun k ↦ (hstartExists k).choose
  have hstart (k : ℕ) : S^[start k] p ∈ W k :=
    (hstartExists k).choose_spec
  refine ⟨start, hlength, ?_⟩
  intro f
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨j, hj⟩ := hG.exists_dist_lt f (show 0 < eps / 4 by positivity)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (hqgeneric f) (eps / 4) (by positivity)
  have herr : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 herr (eps / 4) (by positivity)
  refine ⟨max (max N₁ N₂) j, fun k hk ↦ ?_⟩
  have hkN₁ : N₁ ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hk)
  have hkN₂ : N₂ ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hk)
  have hjk : j < k + 1 := Nat.lt_succ_of_le
    (le_trans (le_max_right _ _) hk)
  have hshadow : dist
      (birkhoffAverage ℝ S (G j) (length k) (S^[start k] p))
      (birkhoffAverage ℝ S (G j) (length k) q) <
        (1 : ℝ) / (k + 1) := by
    exact (Set.mem_iInter₂.mp (hstart k)) j (by simpa using hjk)
  have havg₁ : dist
      (birkhoffAverage ℝ S f (length k) (S^[start k] p))
      (birkhoffAverage ℝ S (G j) (length k) (S^[start k] p)) ≤
        ‖f - G j‖ := by
    simpa only [Real.dist_eq] using
      abs_birkhoffAverage_sub_le_norm S f (G j) (length k) (S^[start k] p)
  have havg₂ : dist
      (birkhoffAverage ℝ S (G j) (length k) q)
      (birkhoffAverage ℝ S f (length k) q) ≤ ‖f - G j‖ := by
    rw [dist_comm]
    simpa only [Real.dist_eq] using
      abs_birkhoffAverage_sub_le_norm S f (G j) (length k) q
  have hnorm : ‖f - G j‖ < eps / 4 := by
    simpa only [dist_eq_norm] using hj
  have herrk : (1 : ℝ) / (k + 1) < eps / 4 := by
    have hnonneg : 0 ≤ (1 : ℝ) / (k + 1) := by positivity
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN₂ k hkN₂
  calc
    dist (birkhoffAverage ℝ S f (length k) (S^[start k] p))
        (∫ x, f x ∂nu) ≤
      dist (birkhoffAverage ℝ S f (length k) (S^[start k] p))
          (birkhoffAverage ℝ S (G j) (length k) (S^[start k] p)) +
        dist (birkhoffAverage ℝ S (G j) (length k) (S^[start k] p))
          (birkhoffAverage ℝ S (G j) (length k) q) +
        dist (birkhoffAverage ℝ S (G j) (length k) q)
          (birkhoffAverage ℝ S f (length k) q) +
        dist (birkhoffAverage ℝ S f (length k) q)
          (∫ x, f x ∂nu) := by
      calc
        _ ≤ dist
              (birkhoffAverage ℝ S f (length k) (S^[start k] p))
              (birkhoffAverage ℝ S f (length k) q) +
            dist (birkhoffAverage ℝ S f (length k) q)
              (∫ x, f x ∂nu) := dist_triangle _ _ _
        _ ≤ (dist
              (birkhoffAverage ℝ S f (length k) (S^[start k] p))
              (birkhoffAverage ℝ S (G j) (length k) (S^[start k] p)) +
            dist
              (birkhoffAverage ℝ S (G j) (length k) (S^[start k] p))
              (birkhoffAverage ℝ S (G j) (length k) q) +
            dist
              (birkhoffAverage ℝ S (G j) (length k) q)
              (birkhoffAverage ℝ S f (length k) q)) +
            dist (birkhoffAverage ℝ S f (length k) q)
              (∫ x, f x ∂nu) := by
          gcongr
          exact dist_triangle4 _ _ _ _
    _ < eps / 4 + eps / 4 + eps / 4 + eps / 4 := by
      exact add_lt_add
        (add_lt_add (add_lt_add (havg₁.trans_lt hnorm)
          (hshadow.trans herrk))
          (havg₂.trans_lt hnorm))
        (hN₁ k hkN₁)
    _ = eps := by ring

/-- The graph extension admits a phase whose pointed orbit is generic along
growing intervals.  This is the topological graph-extension step in the
continuous KMRR reduction. -/
theorem exists_pointed_kroneckerGraph_intervalGeneric
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [CompactSpace X] [T2Space X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) (hTc : Continuous T) (a : X)
    (ha : IsSupportGeneric (fun n ↦ T^[n] a) mu) :
    ∃ z : KroneckerSubgroup T mu hT.toMeasurePreserving,
      ∃ start length : ℕ → ℕ,
        IsGenericAlongOrbitIntervals (kroneckerGraphTransform T mu hT)
          (a, z) (kroneckerGraphMeasure T mu hT) start length := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let : BorelSpace H := inferInstance
  have hex : ∃ q : KroneckerGraphSpace T mu hT,
      q ∈ (kroneckerGraphMeasure T mu hT).support ∧
      ∃ length : ℕ → ℕ, Tendsto length atTop atTop ∧
        ∀ f : BoundedContinuousFunction (KroneckerGraphSpace T mu hT) ℝ,
          Tendsto
            (fun n ↦ birkhoffAverage ℝ (kroneckerGraphTransform T mu hT)
              f (length n) q) atTop
            (nhds (∫ y, f y ∂kroneckerGraphMeasure T mu hT)) :=
    exists_pointwise_generic_subsequence
      (X := KroneckerGraphSpace T mu hT)
      (kroneckerGraphTransform T mu hT)
      (kroneckerGraphMeasure T mu hT)
      (ergodic_kroneckerGraphTransform T mu hT)
  obtain ⟨q, hqsupport, length, hlength, hqgeneric⟩ := hex
  obtain ⟨z, hcluster⟩ :=
    exists_phase_graph_orbit_cluster T mu hT a ha hqsupport
  obtain ⟨start, hgeneric⟩ :=
    exists_genericAlongOrbitIntervals_of_orbit_cluster
      (kroneckerGraphTransform T mu hT)
      (continuous_kroneckerGraphTransform T mu hT hTc)
      (a, z) q (kroneckerGraphMeasure T mu hT)
      hcluster length hlength hqgeneric
  exact ⟨z, start, length, hgeneric⟩


end Erdos656
