module

public import Erdos656.Foundation

@[expose] public section

open Filter Function Set Topology MeasureTheory
open scoped ENNReal Topology ComplexConjugate InnerProductSpace CompactlySupported
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace Erdos656

noncomputable def compMeasurePreservingL2Equiv
    {X : Type*} [MeasurableSpace X]
    (e : X ≃ᵐ X) (mu : Measure X) (he : MeasurePreserving e mu mu) :
    Lp ℂ (2 : ℝ≥0∞) mu ≃ₗᵢ[ℂ] Lp ℂ (2 : ℝ≥0∞) mu := by
  let heinv : MeasurePreserving e.symm mu mu := by
    simpa only [he.map_eq] using e.measurePreserving_symm mu
  exact {
    toFun := Lp.compMeasurePreserving e he
    invFun := Lp.compMeasurePreserving e.symm heinv
    left_inv := by
      intro f
      rw [← Lp.compMeasurePreserving_comp_apply f he heinv]
      rw [Lp.ext_iff]
      filter_upwards [Lp.coeFn_compMeasurePreserving f (he.comp heinv)] with x hx
      simpa only [Function.comp_apply, e.apply_symm_apply] using hx
    right_inv := by
      intro f
      rw [← Lp.compMeasurePreserving_comp_apply f heinv he]
      rw [Lp.ext_iff]
      filter_upwards [Lp.coeFn_compMeasurePreserving f (heinv.comp he)] with x hx
      simpa only [Function.comp_apply, e.symm_apply_apply] using hx
    map_add' := (Lp.compMeasurePreservingₗ ℂ e he).map_add
    map_smul' := (Lp.compMeasurePreservingₗ ℂ e he).map_smul
    norm_map' := fun f => Lp.norm_compMeasurePreserving f he }

noncomputable def koopmanUnitary
    {X : Type*} [MeasurableSpace X]
    (e : X ≃ᵐ X) (mu : Measure X) (he : MeasurePreserving e mu mu) :
    unitary (Lp ℂ (2 : ℝ≥0∞) mu →L[ℂ] Lp ℂ (2 : ℝ≥0∞) mu) :=
  Unitary.linearIsometryEquiv.symm (compMeasurePreservingL2Equiv e mu he)

@[simp] theorem koopmanUnitary_coe
    {X : Type*} [MeasurableSpace X]
    (e : X ≃ᵐ X) (mu : Measure X) (he : MeasurePreserving e mu mu) :
    (koopmanUnitary e mu he :
      Lp ℂ (2 : ℝ≥0∞) mu →L[ℂ] Lp ℂ (2 : ℝ≥0∞) mu) =
      koopmanL2Complex e mu he := by
  rfl

theorem koopman_eigen_ae
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    {lambda : ℂ} {v : Lp ℂ (2 : ℝ≥0∞) mu}
    (hv : koopmanL2Complex T mu hT v = lambda • v) :
    (fun x => v (T x)) =ᵐ[mu] (fun x => lambda * v x) := by
  have hcoe := Lp.ext_iff.mp hv
  filter_upwards [Lp.coeFn_compMeasurePreserving v hT,
    Lp.coeFn_smul lambda v, hcoe] with x hcomp hsmul heq
  exact hcomp.symm.trans (heq.trans hsmul)

theorem eq_smul_of_same_koopman_eigenvalue
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) {lambda : ℂ}
    {v w : Lp ℂ (2 : ℝ≥0∞) mu}
    (hv : koopmanL2Complex T mu hT.1 v = lambda • v)
    (hw0 : w ≠ 0)
    (hw : koopmanL2Complex T mu hT.1 w = lambda • w) :
    ∃ c : ℂ, v = c • w := by
  have hlambda : ‖lambda‖ = 1 :=
    norm_eq_one_of_isKoopmanEigenvalue T mu hT.1 ⟨w, hw0, hw⟩
  have hve := koopman_eigen_ae T mu hT.1 hv
  have hwe := koopman_eigen_ae T mu hT.1 hw
  let q : X → ℂ := fun x => v x * star (w x)
  have hqm : AEStronglyMeasurable q mu :=
    (Lp.aestronglyMeasurable v).mul (Lp.aestronglyMeasurable w).star
  have hqinv : q ∘ T =ᵐ[mu] q := by
    filter_upwards [hve, hwe] with x hvx hwx
    dsimp only [q, Function.comp_apply]
    rw [hvx, hwx]
    rw [star_mul]
    change (lambda * v x) * (conj (w x) * conj lambda) = _
    rw [show lambda * v x * (conj (w x) * conj lambda) =
      (lambda * conj lambda) * (v x * conj (w x)) by ring]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlambda]
    norm_num
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hqm hqinv
  obtain ⟨r, hr0, hr⟩ := eigenvector_norm_ae_const' T mu hT.1 hT hw0 hw
  let d : ℂ := c / ((r : ℂ) ^ 2)
  refine ⟨d, ?_⟩
  rw [Lp.ext_iff]
  filter_upwards [hc, hr, Lp.coeFn_smul d w] with x hcx hrx hdx
  rw [hdx]
  change v x = d * w x
  have hr2 : ((r : ℂ) ^ 2) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr0)
  apply (mul_right_cancel₀ hr2)
  have hqc : v x * conj (w x) = c := by simpa [q] using hcx
  calc
    v x * ((r : ℂ) ^ 2) = v x * (conj (w x) * w x) := by
      rw [← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, hrx, Complex.ofReal_pow]
    _ = c * w x := by rw [← mul_assoc, hqc]
    _ = (d * w x) * ((r : ℂ) ^ 2) := by
      rw [show (d * w x) * ((r : ℂ) ^ 2) =
        (d * ((r : ℂ) ^ 2)) * w x by ring,
        show d * ((r : ℂ) ^ 2) = c by
          exact div_mul_cancel₀ c hr2]

theorem inner_eq_zero_of_orthogonal_chosen_eigenvectors
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) (r : Lp ℂ (2 : ℝ≥0∞) mu)
    (hr : ∀ lambda : KoopmanEigenvalueType T mu hT.1,
      inner ℂ (normalizedKoopmanEigenvector T mu hT.1 lambda) r = 0) :
    ∀ w : Lp ℂ (2 : ℝ≥0∞) mu, ∀ lambda : ℂ,
      koopmanL2Complex T mu hT.1 w = lambda • w → inner ℂ w r = 0 := by
  intro w lambda hw
  by_cases hw0 : w = 0
  · simp [hw0]
  · let lam : KoopmanEigenvalueType T mu hT.1 := ⟨lambda, w, hw0, hw⟩
    obtain ⟨c, hc⟩ := eq_smul_of_same_koopman_eigenvalue T mu hT
      hw (by
        rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]
        norm_num) (normalizedKoopmanEigenvector_eigen T mu hT.1 lam)
    rw [hc, inner_smul_left, hr lam, mul_zero]

theorem normalizedKoopmanEigenvector_factor_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu)
    (lambda : KoopmanEigenvalueType T mu hT.1) :
    ∃ phi : KroneckerSubgroup T mu hT.1 → ℂ, Measurable phi ∧
      (normalizedKoopmanEigenvector T mu hT.1 lambda : X → ℂ) =ᵐ[mu]
        fun x => phi (kroneckerFactorMap T mu hT x) := by
  let : Countable (KoopmanEigenvalueType T mu hT.1) :=
    (countable_koopmanEigenvalues T mu hT.1).to_subtype
  let Z := KroneckerAmbient T mu hT.1
  let H := KroneckerSubgroup T mu hT.1
  obtain ⟨r, hr0, hr⟩ := eigenvector_norm_ae_const' T mu hT.1 hT
    (by rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]; norm_num)
    (normalizedKoopmanEigenvector_eigen T mu hT.1 lambda)
  let base : Additive Circle := kroneckerAmbientBasepoint T mu hT lambda
  let phi : H → ℂ := fun z =>
    (r : ℂ) * ((Additive.toMul (z.1 lambda) : Circle) : ℂ) *
      ((Additive.toMul base : Circle) : ℂ)
  have hphi : Measurable phi := by
    apply Continuous.measurable
    have hcoordcont : Continuous (fun z : H => z.1 lambda) :=
      (continuous_apply lambda).comp continuous_subtype_val
    have hmulcont : Continuous (fun z : H => Additive.toMul (z.1 lambda)) :=
      continuous_toMul.comp hcoordcont
    have hcoecont : Continuous
        (fun z : H => ((Additive.toMul (z.1 lambda) : Circle) : ℂ)) :=
      continuous_subtype_val.comp hmulcont
    exact (continuous_const.mul hcoecont).mul continuous_const
  refine ⟨phi, hphi, ?_⟩
  have hpi := kroneckerFactorMap_coe_ae T mu hT
  have hrep := koopmanEigenfunctionRepresentative_ae_eq T mu hT.1 lambda
  have hne := koopmanEigenfunctionRepresentative_ne_zero_ae T mu hT.1 hT lambda
  filter_upwards [hpi, hrep, hne, hr] with x hpix hrepx hnex hnormx
  have hcoord' :
      ((kroneckerFactorMap T mu hT x : H) : Z) lambda =
        kroneckerAmbientMap T mu hT.1 x lambda - base := by
    simpa [base] using congrFun hpix lambda
  have hcoord :
      kroneckerAmbientMap T mu hT.1 x lambda =
        ((kroneckerFactorMap T mu hT x : H) : Z) lambda + base := by
    calc
      _ = (kroneckerAmbientMap T mu hT.1 x lambda - base) + base := by abel
      _ = _ := by rw [← hcoord']
  have hcircle :
      (koopmanEigenfunctionCircle T mu hT.1 lambda x : ℂ) =
        ((Additive.toMul
          ((((kroneckerFactorMap T mu hT x : H) : Z) lambda)) : Circle) : ℂ) *
          ((Additive.toMul base : Circle) : ℂ) := by
    simpa [kroneckerAmbientMap, base, H, Z] using
      congrArg (fun z : Additive Circle => ((Additive.toMul z : Circle) : ℂ)) hcoord
  have hrepCircle :
      koopmanEigenfunctionRepresentative T mu hT.1 lambda x =
        (r : ℂ) * (koopmanEigenfunctionCircle T mu hT.1 lambda x : ℂ) := by
    unfold koopmanEigenfunctionCircle
    rw [coe_complexToCircle_of_ne_zero hnex]
    rw [hrepx, hnormx]
    field_simp [Complex.ofReal_ne_zero.mpr hr0]
  exact hrepx.symm.trans (hrepCircle.trans (calc
    _ = (r : ℂ) *
        (((Additive.toMul
          ((((kroneckerFactorMap T mu hT x : H) : Z) lambda)) : Circle) : ℂ) *
          ((Additive.toMul base : Circle) : ℂ)) :=
      congrArg (fun z : ℂ => (r : ℂ) * z) hcircle
    _ = phi (kroneckerFactorMap T mu hT x) := by simp [phi, mul_assoc]))

noncomputable def lpTensor
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (r s : Lp ℂ (2 : ℝ≥0∞) mu) :
    Lp ℂ (2 : ℝ≥0∞) (mu.prod mu) := by
  let f : X × X → ℂ := fun p => r p.1 * s p.2
  have hrp := (Lp.aestronglyMeasurable r).comp_fst (ν := mu)
  have hsp := (Lp.aestronglyMeasurable s).comp_snd (μ := mu)
  have hfm : AEStronglyMeasurable f (mu.prod mu) := hrp.mul hsp
  have hrint : Integrable (fun x => ‖r x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp (Lp.memLp r)
  have hsint : Integrable (fun x => ‖s x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable s)).mp (Lp.memLp s)
  have hfint : Integrable (fun p : X × X => ‖f p‖ ^ 2) (mu.prod mu) := by
    convert hrint.mul_prod hsint using 1
    funext p
    simp only [f, norm_mul]
    ring
  exact (memLp_two_iff_integrable_sq_norm hfm).mpr hfint |>.toLp f

theorem lpTensor_coe_ae
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (r s : Lp ℂ (2 : ℝ≥0∞) mu) :
    (lpTensor mu r s : X × X → ℂ) =ᵐ[mu.prod mu]
      fun p => r p.1 * s p.2 := by
  let f : X × X → ℂ := fun p => r p.1 * s p.2
  have hfm : AEStronglyMeasurable f (mu.prod mu) :=
    ((Lp.aestronglyMeasurable r).comp_fst (ν := mu)).mul
      ((Lp.aestronglyMeasurable s).comp_snd (μ := mu))
  have hrint : Integrable (fun x => ‖r x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp (Lp.memLp r)
  have hsint : Integrable (fun x => ‖s x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable s)).mp (Lp.memLp s)
  have hfint : Integrable (fun p : X × X => ‖f p‖ ^ 2) (mu.prod mu) := by
    convert hrint.mul_prod hsint using 1
    funext p
    simp only [f, norm_mul]
    ring
  have hfmem : MemLp f 2 (mu.prod mu) :=
    (memLp_two_iff_integrable_sq_norm hfm).mpr hfint
  exact hfmem.coeFn_toLp

theorem coe_koopmanL2Complex_pow_ae
    {X : Type*} [MeasurableSpace X] (T : X → X)
    (mu : Measure X) (hT : MeasurePreserving T mu mu)
    (v : Lp ℂ (2 : ℝ≥0∞) mu) (k : ℕ) :
    ((((koopmanL2Complex T mu hT) ^ k) v : Lp ℂ 2 mu) : X → ℂ) =ᵐ[mu]
      fun x => v (T^[k] x) := by
  have hfun : (koopmanL2Complex T mu hT : Lp ℂ 2 mu → Lp ℂ 2 mu) =
      Lp.compMeasurePreserving T hT := rfl
  rw [Spectral.pow_continuousLinearMap_apply]
  change (((((koopmanL2Complex T mu hT : Lp ℂ 2 mu → Lp ℂ 2 mu)^[k]) v :
    Lp ℂ 2 mu) : X → ℂ)) =ᵐ[mu] _
  rw [hfun, Lp.compMeasurePreserving_iterate hT k]
  exact Lp.coeFn_compMeasurePreserving v (hT.iterate k)

theorem inner_lpTensor_koopman_pow
    {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X)
    (mu : Measure X) [IsFiniteMeasure mu]
    (he : MeasurePreserving e mu mu)
    (r s : Lp ℂ (2 : ℝ≥0∞) mu) (k : ℕ) :
    inner ℂ (lpTensor mu r s)
        (((koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he)) ^ k)
          (lpTensor mu r s)) =
      inner ℂ r (((koopmanL2Complex e mu he) ^ k) r) *
        inner ℂ s (((koopmanL2Complex e mu he) ^ k) s) := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  have hw := lpTensor_coe_ae mu r s
  have hwk := coe_koopmanL2Complex_pow_ae (Prod.map e e) (mu.prod mu)
    (he.prod he) (lpTensor mu r s) k
  have hrk := coe_koopmanL2Complex_pow_ae e mu he r k
  have hsk := coe_koopmanL2Complex_pow_ae e mu he s k
  have hint : (fun p : X × X => inner ℂ
      (lpTensor mu r s p)
      ((((koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he)) ^ k)
        (lpTensor mu r s)) p)) =ᵐ[mu.prod mu]
      fun p => (r (e^[k] p.1) * conj (r p.1)) *
        (s (e^[k] p.2) * conj (s p.2)) := by
    filter_upwards [hw, hwk,
      (he.prod he).iterate k |>.quasiMeasurePreserving.ae hw] with p hp hpw hpk
    rw [hp, hpw, hpk]
    change inner ℂ (r p.1 * s p.2)
      (r ((diagonalTransform e)^[k] p).1 * s ((diagonalTransform e)^[k] p).2) =
        (r (e^[k] p.1) * conj (r p.1)) *
          (s (e^[k] p.2) * conj (s p.2))
    rw [diagonalTransform_iterate_apply]
    simp only [RCLike.inner_apply, map_mul]
    ring
  rw [integral_congr_ae hint]
  change (∫ p : X × X,
      (fun x => r (e^[k] x) * conj (r x)) p.1 *
        (fun y => s (e^[k] y) * conj (s y)) p.2 ∂mu.prod mu) = _
  calc
    _ = (∫ x, r (e^[k] x) * conj (r x) ∂mu) *
          ∫ y, s (e^[k] y) * conj (s y) ∂mu :=
      integral_prod_mul (fun x => r (e^[k] x) * conj (r x))
        (fun y => s (e^[k] y) * conj (s y))
    _ = _ := by
      congr 1
      · apply integral_congr_ae
        filter_upwards [hrk] with x hx
        rw [hx]
        simp only [RCLike.inner_apply]
      · apply integral_congr_ae
        filter_upwards [hsk] with x hx
        rw [hx]
        simp only [RCLike.inner_apply]

theorem tendsto_lpTensor_average_zero
    {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (he : MeasurePreserving e mu mu)
    (r s : Lp ℂ (2 : ℝ≥0∞) mu)
    (hr : ∀ w : Lp ℂ (2 : ℝ≥0∞) mu, ∀ lambda : ℂ,
      koopmanL2Complex e mu he w = lambda • w → inner ℂ w r = 0) :
    Tendsto (fun n => birkhoffAverage ℂ
      (koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he)) id (n + 1)
      (lpTensor mu r s)) atTop (nhds 0) := by
  let u := koopmanUnitary e mu he
  have hrsq := Spectral.unitary_correlation_mean_square_tendsto_zero u r (by
    intro lambda w hw
    apply hr w lambda
    simpa [u] using hw)
  apply Spectral.tendsto_birkhoffAverage_zero_of_correlation_dominated
    (koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he))
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simpa only [one_mul] using
        le_of_eq (norm_koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he) v))
    (lpTensor mu r s) (fun k => ‖inner ℂ r
      (((koopmanL2Complex e mu he) ^ k) r)‖) (fun _ => norm_nonneg _) hrsq
    (‖s‖ ^ 2) (sq_nonneg _)
  intro k
  rw [inner_lpTensor_koopman_pow e mu he r s k, norm_mul]
  rw [mul_comm (‖s‖ ^ 2)]
  gcongr
  calc
    ‖inner ℂ s (((koopmanL2Complex e mu he) ^ k) s)‖ ≤
        ‖s‖ * ‖((koopmanL2Complex e mu he) ^ k) s‖ :=
      norm_inner_le_norm s (((koopmanL2Complex e mu he) ^ k) s)
    _ = ‖s‖ ^ 2 := by
      rw [show (((koopmanL2Complex e mu he) ^ k) s) =
        Lp.compMeasurePreserving e^[k] (he.iterate k) s by
          rw [Spectral.pow_continuousLinearMap_apply]
          change ((Lp.compMeasurePreserving e he)^[k]) s = _
          rw [Lp.compMeasurePreserving_iterate],
        Lp.norm_compMeasurePreserving]
      exact (pow_two ‖s‖).symm

end Erdos656

namespace Erdos656

open Filter Function Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise Topology

noncomputable def kernelExpectation
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (f : BoundedContinuousFunction X ℝ) (z : Z) : ℝ :=
  ∫ x, f x ∂eta z

theorem stronglyMeasurable_kernelExpectation
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (f : BoundedContinuousFunction X ℝ) :
    StronglyMeasurable (kernelExpectation eta f) := by
  exact f.continuous.stronglyMeasurable.integral_kernel

theorem norm_kernelExpectation_le
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (f : BoundedContinuousFunction X ℝ) (z : Z) :
    ‖kernelExpectation eta f z‖ ≤ ‖f‖ := by
  unfold kernelExpectation
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := eta z) (C := ‖f‖)
      (Eventually.of_forall fun x => f.norm_coe_le_norm x))

noncomputable def kernelExpectationLp
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsFiniteMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (f : BoundedContinuousFunction X ℝ) : Lp ℝ (2 : ℝ≥0∞) m :=
  (MemLp.of_bound (stronglyMeasurable_kernelExpectation eta f).aestronglyMeasurable
    ‖f‖ (Eventually.of_forall (norm_kernelExpectation_le eta f))).toLp
      (kernelExpectation eta f)

theorem kernelExpectationLp_coe_ae
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsFiniteMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (f : BoundedContinuousFunction X ℝ) :
    (kernelExpectationLp m eta f : Z → ℝ) =ᵐ[m] kernelExpectation eta f := by
  exact MemLp.coeFn_toLp _

theorem continuous_haarCorrelation
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [BorelSpace Z] [R1Space Z] [AddCommGroup Z] [ContinuousAdd Z]
    [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z]
    [OpensMeasurableSpace Z]
    (m : Measure Z) [IsLocallyFiniteMeasure m] [m.InnerRegularCompactLTTop]
    [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    Continuous (fun p : Z × Z =>
      inner ℝ ((DomAddAct.mk p.1) +ᵥ u) ((DomAddAct.mk p.2) +ᵥ v)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : ContinuousVAdd Zᵈᵃᵃ (Lp ℝ (2 : ℝ≥0∞) m) :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
  exact ((DomAddAct.continuous_mk.comp continuous_fst).vadd continuous_const).inner
    ((DomAddAct.continuous_mk.comp continuous_snd).vadd continuous_const)

theorem inner_domAddAct_eq_integral
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    (m : Measure Z) [IsFiniteMeasure m]
    [VAddInvariantMeasure Z Z m] [MeasurableConstVAdd Z Z]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) (r s : Z) :
    inner ℝ ((DomAddAct.mk r) +ᵥ u) ((DomAddAct.mk s) +ᵥ v) =
      ∫ z, u (r + z) * v (s + z) ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk r) u,
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk s) v] with z hu hv
  rw [hu, hv]
  simp [vadd_eq_add, RCLike.inner_apply, mul_comm]

noncomputable def separatedBCF
    {X : Type*} [TopologicalSpace X]
    (f g : BoundedContinuousFunction X ℝ) :
    BoundedContinuousFunction (X × X) ℝ :=
  f.compContinuous ⟨Prod.fst, continuous_fst⟩ *
    g.compContinuous ⟨Prod.snd, continuous_snd⟩

@[simp] theorem separatedBCF_apply
    {X : Type*} [TopologicalSpace X]
    (f g : BoundedContinuousFunction X ℝ) (p : X × X) :
    separatedBCF f g p = f p.1 * g p.2 := rfl

theorem integral_relativeProductProbability_separated
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X]
    [Add Z] [MeasurableAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (f g : BoundedContinuousFunction X ℝ) (r s : Z) :
    ∫ p, f p.1 * g p.2 ∂(relativeProductProbability m eta r s : Measure (X × X)) =
      ∫ z, kernelExpectation eta f (z + r) *
        kernelExpectation eta g (z + s) ∂m := by
  let F := separatedBCF f g
  have hF : Integrable (fun p : X × X => f p.1 * g p.2)
      (relativeProductProbability m eta r s : Measure (X × X)) := by
    have hF' := F.integrable
      (relativeProductProbability m eta r s : Measure (X × X))
    change Integrable (fun p : X × X => f p.1 * g p.2)
      (relativeProductProbability m eta r s : Measure (X × X)) at hF'
    exact hF'
  rw [relativeProductProbability_coe, Measure.comp_eq_comp_const_apply] at hF ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hF]
  simp only [Kernel.const_apply]
  congr 1
  funext z
  rw [relativeProductKernel_apply, MeasureTheory.integral_prod_mul]
  rfl

theorem componentMoment_factorComponent_separated_eq_inner
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [VAddInvariantMeasure Z Z m] [Measure.IsAddLeftInvariant m]
    [MeasurableConstVAdd Z Z]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (f g : BoundedContinuousFunction X ℝ) (p : X × X) :
    componentMoment (fun q => factorComponent m eta pi q) (separatedBCF f g) p =
      inner ℝ ((DomAddAct.mk (pi p.1)) +ᵥ kernelExpectationLp m eta f)
        ((DomAddAct.mk (pi p.2)) +ᵥ kernelExpectationLp m eta g) := by
  rw [componentMoment, factorComponent]
  simp only [separatedBCF_apply]
  rw [integral_relativeProductProbability_separated]
  rw [inner_domAddAct_eq_integral]
  apply integral_congr_ae
  have hf := (quasiMeasurePreserving_add_right m (pi p.1)).ae
    (kernelExpectationLp_coe_ae m eta f)
  have hg := (quasiMeasurePreserving_add_right m (pi p.2)).ae
    (kernelExpectationLp_coe_ae m eta g)
  filter_upwards [hf, hg] with z hfz hgz
  simpa only [add_comm] using congrArg₂ (· * ·) hfz.symm hgz.symm

theorem continuous_componentMoment_factorComponent_separated
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace Z] [BorelSpace Z] [R1Space Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Continuous pi)
    (f g : BoundedContinuousFunction X ℝ) :
    Continuous (componentMoment (fun q => factorComponent m eta pi q)
      (separatedBCF f g)) := by
  have hcorr := (continuous_haarCorrelation m
    (kernelExpectationLp m eta f) (kernelExpectationLp m eta g)).comp
      ((hpi.comp continuous_fst).prodMk (hpi.comp continuous_snd))
  apply hcorr.congr
  intro p
  exact (componentMoment_factorComponent_separated_eq_inner
    m eta pi f g p).symm

noncomputable def separatedContinuousMap
    {X : Type*} [TopologicalSpace X]
    (f g : C(X, ℝ)) : C(X × X, ℝ) :=
  f.comp ⟨Prod.fst, continuous_fst⟩ *
    g.comp ⟨Prod.snd, continuous_snd⟩

@[simp] theorem separatedContinuousMap_apply
    {X : Type*} [TopologicalSpace X]
    (f g : C(X, ℝ)) (p : X × X) :
    separatedContinuousMap f g p = f p.1 * g p.2 := rfl

noncomputable def separatedContinuousSubalgebra
    (X : Type*) [TopologicalSpace X] : Subalgebra ℝ C(X × X, ℝ) := by
  let S : Set C(X × X, ℝ) :=
    Set.range (fun fg : C(X, ℝ) × C(X, ℝ) =>
      separatedContinuousMap fg.1 fg.2)
  let M : Submodule ℝ C(X × X, ℝ) := Submodule.span ℝ S
  have hmul : ∀ {a b : C(X × X, ℝ)}, a ∈ M → b ∈ M → a * b ∈ M := by
    intro a b ha hb
    refine Submodule.span_induction
      (p := fun a _ => ∀ b, b ∈ M → a * b ∈ M) ?_ ?_ ?_ ?_ ha b hb
    · intro a ha b hb
      refine Submodule.span_induction
        (p := fun b _ => a * b ∈ M) ?_ ?_ ?_ ?_ hb
      · intro b hb
        rcases ha with ⟨fg, rfl⟩
        rcases hb with ⟨uv, rfl⟩
        apply Submodule.subset_span
        refine ⟨(fg.1 * uv.1, fg.2 * uv.2), ?_⟩
        ext p
        simp only [separatedContinuousMap_apply, ContinuousMap.mul_apply]
        ring
      · simp
      · intro x y hx hy ihx ihy
        simpa only [mul_add] using M.add_mem ihx ihy
      · intro r x hx ih
        have h := M.smul_mem r ih
        convert h using 1
        ext p
        simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
        ring
    · intro b hb
      simp
    · intro x y hx hy ihx ihy b hb
      simpa only [add_mul] using M.add_mem (ihx b hb) (ihy b hb)
    · intro r x hx ih b hb
      have h := M.smul_mem r (ih b hb)
      convert h using 1
      ext p
      simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
      ring
  exact
    { carrier := M
      mul_mem' := hmul
      one_mem' := by
        apply Submodule.subset_span
        refine ⟨(1, 1), ?_⟩
        ext p
        simp [separatedContinuousMap]
      add_mem' := M.add_mem
      zero_mem' := M.zero_mem
      algebraMap_mem' := by
        intro r
        change (algebraMap ℝ C(X × X, ℝ)) r ∈ M
        have h1 : (1 : C(X × X, ℝ)) ∈ M := by
          apply Submodule.subset_span
          refine ⟨(1, 1), ?_⟩
          ext p
          simp [separatedContinuousMap]
        have h := M.smul_mem r h1
        simpa only [Algebra.smul_def, mul_one] using h }

theorem separatedContinuousSubalgebra_separatesPoints
    (X : Type*) [PseudoMetricSpace X] [T2Space X] :
    (separatedContinuousSubalgebra X).SeparatesPoints := by
  let : MetricSpace X := MetricSpace.ofT0PseudoMetricSpace X
  intro p q hpq
  by_cases hfst : p.1 = q.1
  · have hsnd : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfst h)
    let f : C(X, ℝ) := 1
    let g : C(X, ℝ) := ⟨fun x => dist x p.2, continuous_id.dist continuous_const⟩
    refine ⟨separatedContinuousMap f g, ⟨separatedContinuousMap f g, ?_, rfl⟩, ?_⟩
    · change separatedContinuousMap f g ∈
        Submodule.span ℝ (Set.range (fun fg : C(X, ℝ) × C(X, ℝ) =>
          separatedContinuousMap fg.1 fg.2))
      exact Submodule.subset_span ⟨(f, g), rfl⟩
    · simp only [separatedContinuousMap_apply, f, g, ContinuousMap.one_apply,
        one_mul, ContinuousMap.coe_mk, dist_self]
      exact (dist_ne_zero.mpr (Ne.symm hsnd)).symm
  · let f : C(X, ℝ) := ⟨fun x => dist x p.1, continuous_id.dist continuous_const⟩
    let g : C(X, ℝ) := 1
    refine ⟨separatedContinuousMap f g, ⟨separatedContinuousMap f g, ?_, rfl⟩, ?_⟩
    · change separatedContinuousMap f g ∈
        Submodule.span ℝ (Set.range (fun fg : C(X, ℝ) × C(X, ℝ) =>
          separatedContinuousMap fg.1 fg.2))
      exact Submodule.subset_span ⟨(f, g), rfl⟩
    · simp only [separatedContinuousMap_apply, f, g, ContinuousMap.one_apply,
        mul_one, ContinuousMap.coe_mk, dist_self]
      exact (dist_ne_zero.mpr (Ne.symm hfst)).symm

theorem continuous_integral_factorComponent_of_mem_separatedContinuousSubalgebra
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace Z] [BorelSpace Z] [R1Space Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    [PseudoMetricSpace X] [CompactSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Continuous pi)
    (F : C(X × X, ℝ)) (hF : F ∈ separatedContinuousSubalgebra X) :
    Continuous (fun p : X × X =>
      ∫ q, F q ∂(factorComponent m eta pi p : Measure (X × X))) := by
  change F ∈ Submodule.span ℝ
    (Set.range (fun fg : C(X, ℝ) × C(X, ℝ) =>
      separatedContinuousMap fg.1 fg.2)) at hF
  refine Submodule.span_induction
    (p := fun F _ => Continuous (fun p : X × X =>
      ∫ q, F q ∂(factorComponent m eta pi p : Measure (X × X))))
    ?_ ?_ ?_ ?_ hF
  · intro F hF
    rcases hF with ⟨fg, rfl⟩
    let f := BoundedContinuousFunction.mkOfCompact fg.1
    let g := BoundedContinuousFunction.mkOfCompact fg.2
    have h := continuous_componentMoment_factorComponent_separated
      m eta pi hpi f g
    apply h.congr
    intro p
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      rfl
  · simpa using (continuous_const : Continuous (fun _ : X × X => (0 : ℝ)))
  · intro F G hFs hGs hF hG
    have h := hF.add hG
    apply h.congr
    intro p
    change (∫ q, F q ∂(factorComponent m eta pi p : Measure (X × X))) +
        ∫ q, G q ∂(factorComponent m eta pi p : Measure (X × X)) =
      ∫ q, F q + G q ∂(factorComponent m eta pi p : Measure (X × X))
    exact (integral_add
      ((BoundedContinuousFunction.mkOfCompact F).integrable _)
      ((BoundedContinuousFunction.mkOfCompact G).integrable _)).symm
  · intro r F hFs hF
    have h := (continuous_const : Continuous (fun _ : X × X => r)).mul hF
    convert h using 1
    funext p
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
    rfl

theorem continuous_factorComponent
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace Z] [BorelSpace Z] [R1Space Z]
    [AddCommGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    [PseudoMetricSpace X] [CompactSpace X] [T2Space X] [BorelSpace X]
    [SecondCountableTopology X]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Continuous pi) :
    Continuous (factorComponent m eta pi) := by
  rw [MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro F
  rw [Metric.continuous_iff]
  intro p eps heps
  obtain ⟨G, hGapprox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (separatedContinuousSubalgebra X)
      (separatedContinuousSubalgebra_separatesPoints X) F (eps / 3) (by positivity)
  have hGc : Continuous (fun p : X × X =>
      ∫ q, (G : C(X × X, ℝ)) q
        ∂(factorComponent m eta pi p : Measure (X × X))) :=
    continuous_integral_factorComponent_of_mem_separatedContinuousSubalgebra
      m eta pi hpi G G.property
  obtain ⟨delta, hdelta, hGnear⟩ :=
    (Metric.continuous_iff.mp hGc p (eps / 3) (by positivity))
  refine ⟨delta, hdelta, ?_⟩
  intro x hx
  have hFGnorm :
      ‖BoundedContinuousFunction.mkOfCompact F -
          BoundedContinuousFunction.mkOfCompact (G : C(X × X, ℝ))‖ < eps / 3 := by
    calc
      _ = ‖BoundedContinuousFunction.mkOfCompact
          (F - (G : C(X × X, ℝ)))‖ := by
            rw [BoundedContinuousFunction.mkOfCompact_sub]
      _ = ‖F - (G : C(X × X, ℝ))‖ :=
        BoundedContinuousFunction.norm_mkOfCompact _
      _ = ‖(G : C(X × X, ℝ)) - F‖ := norm_sub_rev _ _
      _ < eps / 3 := hGapprox
  have hGFnorm :
      ‖BoundedContinuousFunction.mkOfCompact (G : C(X × X, ℝ)) -
          BoundedContinuousFunction.mkOfCompact F‖ < eps / 3 := by
    simpa only [norm_sub_rev] using hFGnorm
  have hleft : dist
      (∫ q, F q ∂(factorComponent m eta pi x : Measure (X × X)))
      (∫ q, (G : C(X × X, ℝ)) q
        ∂(factorComponent m eta pi x : Measure (X × X))) < eps / 3 := by
    exact (abs_integral_sub_le_norm
      (factorComponent m eta pi x : Measure (X × X))
      (BoundedContinuousFunction.mkOfCompact F)
      (BoundedContinuousFunction.mkOfCompact (G : C(X × X, ℝ)))).trans_lt hFGnorm
  have hright : dist
      (∫ q, (G : C(X × X, ℝ)) q
        ∂(factorComponent m eta pi p : Measure (X × X)))
      (∫ q, F q ∂(factorComponent m eta pi p : Measure (X × X))) < eps / 3 := by
    exact (abs_integral_sub_le_norm
      (factorComponent m eta pi p : Measure (X × X))
      (BoundedContinuousFunction.mkOfCompact (G : C(X × X, ℝ)))
      (BoundedContinuousFunction.mkOfCompact F)).trans_lt hGFnorm
  calc
    dist (∫ q, F q ∂(factorComponent m eta pi x : Measure (X × X)))
        (∫ q, F q ∂(factorComponent m eta pi p : Measure (X × X))) ≤
      dist (∫ q, F q ∂(factorComponent m eta pi x : Measure (X × X)))
          (∫ q, (G : C(X × X, ℝ)) q
            ∂(factorComponent m eta pi x : Measure (X × X))) +
        dist (∫ q, (G : C(X × X, ℝ)) q
            ∂(factorComponent m eta pi x : Measure (X × X)))
          (∫ q, (G : C(X × X, ℝ)) q
            ∂(factorComponent m eta pi p : Measure (X × X))) +
        dist (∫ q, (G : C(X × X, ℝ)) q
            ∂(factorComponent m eta pi p : Measure (X × X)))
          (∫ q, F q ∂(factorComponent m eta pi p : Measure (X × X))) :=
      dist_triangle4 _ _ _ _
    _ < eps / 3 + eps / 3 + eps / 3 :=
      add_lt_add (add_lt_add hleft (hGnear x hx)) hright
    _ = eps := by ring

end Erdos656
namespace Erdos656

open Filter Function Set Topology MeasureTheory
open ProbabilityTheory
open scoped ENNReal Pointwise Topology

/-- Fiberwise convergence in measure over a probability product promotes to
convergence in measure on the product. -/
theorem tendstoInMeasure_prod_of_forall_fiber
    {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [PseudoMetricSpace E]
    (mu : Measure A) (nu : Measure B) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (f : ℕ → A × B → E) (g : A × B → E)
    (hmeas : ∀ n, Measurable (fun p => dist (f n p) (g p)))
    (hfiber : ∀ a, TendstoInMeasure nu
      (fun n b => f n (a, b)) atTop (fun b => g (a, b))) :
    TendstoInMeasure (mu.prod nu) f atTop g := by
  rw [tendstoInMeasure_iff_dist]
  intro eps heps
  let bad : ℕ → Set (A × B) := fun n => {p | eps ≤ dist (f n p) (g p)}
  have hbad (n : ℕ) : MeasurableSet (bad n) :=
    measurableSet_le measurable_const (hmeas n)
  let sectionMeasure : ℕ → A → ℝ≥0∞ := fun n a =>
    nu (Prod.mk a ⁻¹' bad n)
  have hsectionMeas (n : ℕ) : Measurable (sectionMeasure n) :=
    measurable_measure_prodMk_left (hbad n)
  have hsectionLim (a : A) : Tendsto (fun n => sectionMeasure n a)
      atTop (nhds 0) := by
    simpa only [sectionMeasure, bad, Set.preimage_ofPred_eq,
      Prod.mk.eta] using
      (tendstoInMeasure_iff_dist.mp (hfiber a) eps heps)
  have hdom : ∀ n, sectionMeasure n ≤ᵐ[mu] fun _ => (1 : ℝ≥0∞) := by
    intro n
    exact Eventually.of_forall fun a => by
      exact (measure_mono (subset_univ _)).trans_eq measure_univ
  have hfin : (∫⁻ _ : A, (1 : ℝ≥0∞) ∂mu) ≠ ∞ := by simp
  have hlim := tendsto_lintegral_of_dominated_convergence
    (fun _ : A => (1 : ℝ≥0∞)) hsectionMeas hdom hfin
    (Eventually.of_forall hsectionLim)
  simpa only [Measure.prod_apply (hbad _), sectionMeasure, bad,
    lintegral_zero] using hlim

theorem tendstoInMeasure_comp_measurePreserving
    {X E : Type*} [MeasurableSpace X] [PseudoEMetricSpace E]
    {mu : Measure X} {f : ℕ → X → E} {g : X → E}
    (h : TendstoInMeasure mu f atTop g) (S : X → X)
    (hS : MeasurePreserving S mu mu) :
    TendstoInMeasure mu (fun n x => f n (S x)) atTop (fun x => g (S x)) := by
  intro eps heps
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (h eps heps) (Eventually.of_forall fun _ => zero_le) ?_
  exact Eventually.of_forall fun n => by
    have hsub : {x | eps ≤ edist (f n (S x)) (g (S x))} ⊆
        S ⁻¹' {y | eps ≤ edist (f n y) (g y)} := fun x hx => hx
    exact (measure_mono hsub).trans (hS.measure_preimage_le _)

/-- The one-dimensional observable obtained after shearing a diagonal pair
orbit into a difference coordinate and a moving coordinate. -/
noncomputable def haarFiberObservable
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (u v : BoundedContinuousFunction Z ℝ) (d : Z) :
    BoundedContinuousFunction Z ℝ :=
  u * v.compContinuous ⟨fun q => q + d, continuous_id.add continuous_const⟩

@[simp] theorem haarFiberObservable_apply
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (u v : BoundedContinuousFunction Z ℝ) (d q : Z) :
    haarFiberObservable u v d q = u q * v (q + d) := rfl

noncomputable def haarFiberMean
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [Add Z] [ContinuousAdd Z]
    (m : Measure Z) (u v : BoundedContinuousFunction Z ℝ) (d : Z) : ℝ :=
  ∫ q, haarFiberObservable u v d q ∂m

theorem continuous_haarFiberMean
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z]
    [BorelSpace Z] [CompactSpace Z] [Add Z] [ContinuousAdd Z]
    (m : Measure Z) [IsFiniteMeasure m]
    (u v : BoundedContinuousFunction Z ℝ) :
    Continuous (haarFiberMean m u v) := by
  change Continuous (fun d : Z => ∫ q, u q * v (q + d) ∂m)
  have huncurry : Continuous (Function.uncurry
      (fun d q : Z => u q * v (q + d))) := by
    exact (u.continuous.comp continuous_snd).mul
      (v.continuous.comp (continuous_snd.add continuous_fst))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := m) huncurry (s := Set.univ) isCompact_univ)

theorem addRotation_iterate_apply
    {Z : Type*} [AddCommMonoid Z] (a q : Z) (n : ℕ) :
    (fun z : Z => a + z)^[n] q = n • a + q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, succ_nsmul]
      abel

@[simp] theorem fiberTransform_iterate_apply
    {Z : Type*} (R : Z → Z) (n : ℕ) (p : Z × Z) :
    (fun q : Z × Z => (q.1, R q.2))^[n] p = (p.1, R^[n] p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        Function.iterate_succ_apply']

theorem tendstoInMeasure_haarFiberAverage
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z]
    [AddCommGroup Z] [ContinuousAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (a : Z) (hrot : Ergodic (fun z => a + z) m)
    (u v : BoundedContinuousFunction Z ℝ) (d : Z) :
    TendstoInMeasure m
      (fun n q => birkhoffAverage ℝ (fun z => a + z)
        (haarFiberObservable u v d) n q)
      atTop (fun _ => haarFiberMean m u v d) := by
  let R : Z → Z := fun z => a + z
  let h : BoundedContinuousFunction Z ℝ := haarFiberObservable u v d
  have hlp := meanErgodic_limit_ae_const R m hrot h
  have hm := tendstoInMeasure_of_tendsto_Lp hlp
  have hm' : TendstoInMeasure m
      (fun n q => birkhoffAverage ℝ R h n q) atTop
      ((indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top m Set.univ) (haarFiberMean m u v d) :
          Lp ℝ 2 m) : Z → ℝ) := by
    apply TendstoInMeasure.congr_left
      (fun n => coe_birkhoffAverage_toLp_ae R m hrot.1 h n)
    simpa only [h, R, haarFiberMean] using hm
  have hc :
      ((indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top m Set.univ) (haarFiberMean m u v d) :
          Lp ℝ 2 m) : Z → ℝ) =ᵐ[m]
        fun _ => haarFiberMean m u v d := by
    simpa using
      (@indicatorConstLp_coeFn Z ℝ _ 2 m _ Set.univ
        MeasurableSet.univ (measure_ne_top m Set.univ)
        (haarFiberMean m u v d))
  exact TendstoInMeasure.congr_right hc hm'

def haarCoordTransform {Z : Type*} [Add Z] (a : Z) : Z × Z → Z × Z :=
  fun p => (p.1, a + p.2)

noncomputable def haarCoordObservable
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (u v : BoundedContinuousFunction Z ℝ) :
    BoundedContinuousFunction (Z × Z) ℝ :=
  u.compContinuous ⟨Prod.snd, continuous_snd⟩ *
  v.compContinuous ⟨fun p => p.2 + p.1,
    continuous_snd.add continuous_fst⟩

@[simp] theorem haarCoordObservable_apply
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (u v : BoundedContinuousFunction Z ℝ) (p : Z × Z) :
    haarCoordObservable u v p = u p.2 * v (p.2 + p.1) := rfl

noncomputable def haarCoordAverage
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) (p : Z × Z) : ℝ :=
  birkhoffAverage ℝ (haarCoordTransform a) (haarCoordObservable u v) n p

noncomputable def haarCoordTarget
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [Add Z] [ContinuousAdd Z]
    (m : Measure Z) (u v : BoundedContinuousFunction Z ℝ) (p : Z × Z) : ℝ :=
  haarFiberMean m u v p.1

theorem continuous_haarCoordAverage
    {Z : Type*} [PseudoMetricSpace Z] [Add Z] [ContinuousAdd Z]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) :
    Continuous (haarCoordAverage a u v n) := by
  exact continuous_birkhoffAverage_of_continuous (haarCoordTransform a)
    (continuous_fst.prodMk
      ((continuous_const.add continuous_id).comp continuous_snd))
    (haarCoordObservable u v) (haarCoordObservable u v).continuous n

theorem haarCoordAverage_mk
    {Z : Type*} [TopologicalSpace Z] [AddCommMonoid Z] [ContinuousAdd Z]
    (a d q : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) :
    haarCoordAverage a u v n (d, q) =
      birkhoffAverage ℝ (fun z => a + z) (haarFiberObservable u v d) n q := by
  unfold haarCoordAverage haarCoordTransform birkhoffAverage birkhoffSum
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [fiberTransform_iterate_apply]
  simp [haarFiberObservable, haarCoordObservable]

theorem tendstoInMeasure_haarCoord
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z]
    [AddCommGroup Z] [ContinuousAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (a : Z) (hrot : Ergodic (fun z => a + z) m)
    (u v : BoundedContinuousFunction Z ℝ) :
    TendstoInMeasure (m.prod m) (haarCoordAverage a u v) atTop
      (haarCoordTarget m u v) := by
  apply tendstoInMeasure_prod_of_forall_fiber m m
    (haarCoordAverage a u v) (haarCoordTarget m u v)
  · intro n
    exact (continuous_haarCoordAverage a u v n).dist
      ((continuous_haarFiberMean m u v).comp continuous_fst) |>.measurable
  · intro d
    apply TendstoInMeasure.congr_left (fun n => ?_)
      (tendstoInMeasure_haarFiberAverage m a hrot u v d)
    exact Eventually.of_forall fun q => (haarCoordAverage_mk a d q u v n).symm

def haarDifferenceShear {Z : Type*} [Sub Z] : Z × Z → Z × Z :=
  fun p => (p.2 - p.1, p.1)

theorem measurePreserving_haarDifferenceShear
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [IsFiniteMeasure m] [Measure.IsAddRightInvariant m] :
    MeasurePreserving (haarDifferenceShear : Z × Z → Z × Z)
      (m.prod m) (m.prod m) := by
  exact (Measure.measurePreserving_swap (μ := m) (ν := m)).comp
    (measurePreserving_prod_sub m m)

theorem haarCoordAverage_shear
    {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [ContinuousAdd Z]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) (p : Z × Z) :
    haarCoordAverage a u v n (haarDifferenceShear p) =
      birkhoffAverage ℝ (diagonalTransform (fun z => a + z))
        (separatedBCF u v) n p := by
  unfold haarCoordAverage haarCoordTransform birkhoffAverage birkhoffSum
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [haarCoordObservable_apply,
    separatedBCF_apply, diagonalTransform_iterate_apply,
    fiberTransform_iterate_apply, haarDifferenceShear]
  congr 2
  rw [addRotation_iterate_apply, addRotation_iterate_apply]
  abel

theorem tendstoInMeasure_haarCoord_shear
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z]
    [AddCommGroup Z] [ContinuousAdd Z] [MeasurableAdd₂ Z]
    [MeasurableNeg Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z => a + z) m)
    (u v : BoundedContinuousFunction Z ℝ) :
    TendstoInMeasure (m.prod m)
      (fun n p => haarCoordAverage a u v n (haarDifferenceShear p))
      atTop (fun p => haarCoordTarget m u v (haarDifferenceShear p)) := by
  exact tendstoInMeasure_comp_measurePreserving
    (tendstoInMeasure_haarCoord m a hrot u v)
    haarDifferenceShear (measurePreserving_haarDifferenceShear m)

/-- In a compact ergodic group rotation, diagonal averages of a separated
continuous observable converge in measure to the Haar correlation indexed by
the difference of the two coordinates. -/
theorem tendstoInMeasure_haarDiagonal_separated
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z]
    [AddCommGroup Z] [ContinuousAdd Z] [MeasurableAdd₂ Z]
    [MeasurableNeg Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z => a + z) m)
    (u v : BoundedContinuousFunction Z ℝ) :
    TendstoInMeasure (m.prod m)
      (fun n p => birkhoffAverage ℝ (diagonalTransform (fun z => a + z))
        (separatedBCF u v) n p)
      atTop (fun p => haarFiberMean m u v (p.2 - p.1)) := by
  exact TendstoInMeasure.congr
    (fun n => Eventually.of_forall fun p => haarCoordAverage_shear a u v n p)
    (Eventually.of_forall fun p => rfl)
    (tendstoInMeasure_haarCoord_shear m a hrot u v)

noncomputable def haarDiagonalAverage
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) (p : Z × Z) : ℝ :=
  birkhoffAverage ℝ (diagonalTransform (fun z => a + z))
    (separatedBCF u v) n p

noncomputable def haarDiagonalLimit
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [Sub Z] [Add Z] [ContinuousAdd Z]
    (m : Measure Z) (u v : BoundedContinuousFunction Z ℝ) (p : Z × Z) : ℝ :=
  haarFiberMean m u v (p.2 - p.1)

theorem abs_haarDiagonalAverage_le
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) (p : Z × Z) :
    |haarDiagonalAverage a u v n p| ≤ ‖u‖ * ‖v‖ := by
  have h := abs_birkhoffAverage_sub_le_norm
    (diagonalTransform (fun z : Z => a + z)) (separatedBCF u v)
      (0 : BoundedContinuousFunction (Z × Z) ℝ) n p
  have hzero : birkhoffAverage ℝ (diagonalTransform (fun z : Z => a + z))
      (0 : BoundedContinuousFunction (Z × Z) ℝ) n p = 0 := by
    simp [birkhoffAverage, birkhoffSum]
  rw [hzero, sub_zero] at h
  exact h.trans (calc
    ‖separatedBCF u v - 0‖ = ‖separatedBCF u v‖ := by simp
    _ ≤
        ‖u.compContinuous ⟨Prod.fst, continuous_fst⟩‖ *
          ‖v.compContinuous ⟨Prod.snd, continuous_snd⟩‖ := by
      exact norm_mul_le _ _
    _ ≤ ‖u‖ * ‖v‖ := by
      exact mul_le_mul
        (BoundedContinuousFunction.norm_compContinuous_le u
          ⟨Prod.fst, continuous_fst⟩)
        (BoundedContinuousFunction.norm_compContinuous_le v
          ⟨Prod.snd, continuous_snd⟩)
        (norm_nonneg _) (norm_nonneg _))

theorem abs_haarDiagonalLimit_le
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [OpensMeasurableSpace Z] [AddCommGroup Z] [ContinuousAdd Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (u v : BoundedContinuousFunction Z ℝ) (p : Z × Z) :
    |haarDiagonalLimit m u v p| ≤ ‖u‖ * ‖v‖ := by
  unfold haarDiagonalLimit haarFiberMean
  change ‖∫ q, haarFiberObservable u v (p.2 - p.1) q ∂m‖ ≤ _
  calc
    _ ≤ ‖haarFiberObservable u v (p.2 - p.1)‖ :=
      (haarFiberObservable u v (p.2 - p.1)).norm_integral_le_norm m
    _ ≤ ‖u‖ *
        ‖v.compContinuous ⟨fun q => q + (p.2 - p.1),
          continuous_id.add continuous_const⟩‖ := by
      exact norm_mul_le _ _
    _ ≤ ‖u‖ * ‖v‖ := by
      gcongr
      exact BoundedContinuousFunction.norm_compContinuous_le v
        ⟨fun q => q + (p.2 - p.1), continuous_id.add continuous_const⟩

theorem haarDiagonalAverageMemLp
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    [AddCommGroup Z] [ContinuousAdd Z]
    (m : Measure Z) [IsFiniteMeasure m]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) (n : ℕ) :
    MemLp (haarDiagonalAverage a u v n) 2 (m.prod m) :=
  MemLp.of_bound
    ((continuous_birkhoffAverage_of_continuous
      (diagonalTransform (fun z : Z => a + z))
      (continuous_diagonalTransform (continuous_const.add continuous_id))
      (separatedBCF u v) (separatedBCF u v).continuous n).aestronglyMeasurable)
    (‖u‖ * ‖v‖) (Eventually.of_forall fun p => by
      simpa only [haarDiagonalAverage, Real.norm_eq_abs] using
        abs_haarDiagonalAverage_le a u v n p)

theorem haarDiagonalLimitMemLp
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (u v : BoundedContinuousFunction Z ℝ) :
    MemLp (haarDiagonalLimit m u v) 2 (m.prod m) :=
  MemLp.of_bound
    (((continuous_haarFiberMean m u v).comp
      (continuous_snd.sub continuous_fst)).aestronglyMeasurable)
    (‖u‖ * ‖v‖) (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using abs_haarDiagonalLimit_le m u v p)

theorem unifIntegrable_haarDiagonalAverage
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    [AddCommGroup Z] [ContinuousAdd Z]
    (m : Measure Z) [IsFiniteMeasure m]
    (a : Z) (u v : BoundedContinuousFunction Z ℝ) :
    UnifIntegrable (haarDiagonalAverage a u v) 2 (m.prod m) := by
  refine unifIntegrable_of (μ := m.prod m)
    (f := haarDiagonalAverage a u v) (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num)
    (fun n => (haarDiagonalAverageMemLp m a u v n).aestronglyMeasurable) ?_
  intro eps heps
  let C : NNReal := ⟨‖u‖ * ‖v‖ + 1, by positivity⟩
  refine ⟨C, fun n => ?_⟩
  have hset : {p : Z × Z | C ≤ ‖haarDiagonalAverage a u v n p‖₊} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro p hp
    change C ≤ ‖haarDiagonalAverage a u v n p‖₊ at hp
    have hp' : (C : ℝ) ≤ ‖haarDiagonalAverage a u v n p‖ := by
      exact_mod_cast hp
    have hle := abs_haarDiagonalAverage_le a u v n p
    have hlt : ‖haarDiagonalAverage a u v n p‖ < C := by
      change |haarDiagonalAverage a u v n p| < ‖u‖ * ‖v‖ + 1
      linarith
    exact (not_lt_of_ge hp') hlt
  rw [hset]
  simp

theorem tendsto_haarDiagonalAverage_toLp
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [MeasurableAdd₂ Z]
    [MeasurableNeg Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z => a + z) m)
    (u v : BoundedContinuousFunction Z ℝ) :
    Tendsto
      (fun n => (haarDiagonalAverageMemLp m a u v n).toLp
        (haarDiagonalAverage a u v n)) atTop
      (nhds ((haarDiagonalLimitMemLp m u v).toLp
        (haarDiagonalLimit m u v))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun n => (haarDiagonalAverageMemLp m a u v n).toLp
      (haarDiagonalAverage a u v n))
    (haarDiagonalLimit m u v) (haarDiagonalLimitMemLp m u v)).2
  have hvitali := tendsto_Lp_finite_of_tendstoInMeasure (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num)
    (fun n => (haarDiagonalAverageMemLp m a u v n).aestronglyMeasurable)
    (haarDiagonalLimitMemLp m u v)
    (unifIntegrable_haarDiagonalAverage m a u v)
    (tendstoInMeasure_haarDiagonal_separated m a hrot u v)
  have heq :
      (fun n => eLpNorm
        ((fun p => ((haarDiagonalAverageMemLp m a u v n).toLp
          (haarDiagonalAverage a u v n)) p) - haarDiagonalLimit m u v)
          2 (m.prod m)) =
      (fun n => eLpNorm
        (haarDiagonalAverage a u v n - haarDiagonalLimit m u v)
          2 (m.prod m)) := by
    funext n
    apply eLpNorm_congr_ae
    exact (haarDiagonalAverageMemLp m a u v n).coeFn_toLp.sub
      EventuallyEq.rfl
  rw [heq]
  exact hvitali

noncomputable def lpTensorReal
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (r s : Lp ℝ (2 : ℝ≥0∞) mu) :
    Lp ℝ (2 : ℝ≥0∞) (mu.prod mu) := by
  let f : X × X → ℝ := fun p => r p.1 * s p.2
  have hfm : AEStronglyMeasurable f (mu.prod mu) :=
    ((Lp.aestronglyMeasurable r).comp_fst (ν := mu)).mul
      ((Lp.aestronglyMeasurable s).comp_snd (μ := mu))
  have hrint : Integrable (fun x => ‖r x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp (Lp.memLp r)
  have hsint : Integrable (fun x => ‖s x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable s)).mp (Lp.memLp s)
  have hfint : Integrable (fun p : X × X => ‖f p‖ ^ 2) (mu.prod mu) := by
    convert hrint.mul_prod hsint using 1
    funext p
    simp only [f, norm_mul]
    ring
  exact ((memLp_two_iff_integrable_sq_norm hfm).mpr hfint).toLp f

theorem lpTensorReal_coe_ae
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (r s : Lp ℝ (2 : ℝ≥0∞) mu) :
    (lpTensorReal mu r s : X × X → ℝ) =ᵐ[mu.prod mu]
      fun p => r p.1 * s p.2 := by
  let f : X × X → ℝ := fun p => r p.1 * s p.2
  have hfm : AEStronglyMeasurable f (mu.prod mu) :=
    ((Lp.aestronglyMeasurable r).comp_fst (ν := mu)).mul
      ((Lp.aestronglyMeasurable s).comp_snd (μ := mu))
  have hrint : Integrable (fun x => ‖r x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp (Lp.memLp r)
  have hsint : Integrable (fun x => ‖s x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable s)).mp (Lp.memLp s)
  have hfint : Integrable (fun p : X × X => ‖f p‖ ^ 2) (mu.prod mu) := by
    convert hrint.mul_prod hsint using 1
    funext p
    simp only [f, norm_mul]
    ring
  exact ((memLp_two_iff_integrable_sq_norm hfm).mpr hfint).coeFn_toLp

theorem inner_lpTensorReal_self
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (r s : Lp ℝ (2 : ℝ≥0∞) mu) :
    inner ℝ (lpTensorReal mu r s) (lpTensorReal mu r s) =
      inner ℝ r r * inner ℝ s s := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  rw [integral_congr_ae]
  · change (∫ p : X × X,
        (fun x => r x * r x) p.1 * (fun y => s y * s y) p.2 ∂mu.prod mu) =
      (∫ x, r x * r x ∂mu) * ∫ y, s y * s y ∂mu
    exact integral_prod_mul (fun x => r x * r x) (fun y => s y * s y)
  · filter_upwards [lpTensorReal_coe_ae mu r s] with p hp
    rw [hp]
    simp only [RCLike.inner_apply, conj_trivial]
    ring

theorem norm_lpTensorReal
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (r s : Lp ℝ (2 : ℝ≥0∞) mu) :
    ‖lpTensorReal mu r s‖ = ‖r‖ * ‖s‖ := by
  have h := inner_lpTensorReal_self mu r s
  simp only [real_inner_self_eq_norm_sq] at h
  have hrs : 0 ≤ ‖r‖ * ‖s‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (lpTensorReal mu r s)]

theorem lpTensorReal_add_left
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (r₁ r₂ s : Lp ℝ (2 : ℝ≥0∞) mu) :
    lpTensorReal mu (r₁ + r₂) s =
      lpTensorReal mu r₁ s + lpTensorReal mu r₂ s := by
  apply Lp.ext
  have hfst : MeasurePreserving Prod.fst (mu.prod mu) mu :=
    ⟨measurable_fst, by simp⟩
  have hr := hfst.quasiMeasurePreserving.ae (Lp.coeFn_add r₁ r₂)
  filter_upwards [lpTensorReal_coe_ae mu (r₁ + r₂) s,
    lpTensorReal_coe_ae mu r₁ s, lpTensorReal_coe_ae mu r₂ s,
    hr,
    Lp.coeFn_add (lpTensorReal mu r₁ s) (lpTensorReal mu r₂ s)] with p h h₁ h₂ hr hadd
  rw [h, hadd]
  change (r₁ + r₂) p.1 * s p.2 =
    lpTensorReal mu r₁ s p + lpTensorReal mu r₂ s p
  rw [h₁, h₂, hr]
  simp only [Pi.add_apply]
  ring

theorem lpTensorReal_add_right
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (r s₁ s₂ : Lp ℝ (2 : ℝ≥0∞) mu) :
    lpTensorReal mu r (s₁ + s₂) =
      lpTensorReal mu r s₁ + lpTensorReal mu r s₂ := by
  apply Lp.ext
  have hsnd : MeasurePreserving Prod.snd (mu.prod mu) mu :=
    ⟨measurable_snd, by simp⟩
  have hs := hsnd.quasiMeasurePreserving.ae (Lp.coeFn_add s₁ s₂)
  filter_upwards [lpTensorReal_coe_ae mu r (s₁ + s₂),
    lpTensorReal_coe_ae mu r s₁, lpTensorReal_coe_ae mu r s₂,
    hs,
    Lp.coeFn_add (lpTensorReal mu r s₁) (lpTensorReal mu r s₂)] with p h h₁ h₂ hs hadd
  rw [h, hadd]
  change r p.1 * (s₁ + s₂) p.2 =
    lpTensorReal mu r s₁ p + lpTensorReal mu r s₂ p
  rw [h₁, h₂, hs]
  simp only [Pi.add_apply]
  ring

theorem lpTensorReal_sub_left
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (r₁ r₂ s : Lp ℝ (2 : ℝ≥0∞) mu) :
    lpTensorReal mu (r₁ - r₂) s =
      lpTensorReal mu r₁ s - lpTensorReal mu r₂ s := by
  apply Lp.ext
  have hfst : MeasurePreserving Prod.fst (mu.prod mu) mu :=
    measurePreserving_fst
  have hr := hfst.quasiMeasurePreserving.ae (Lp.coeFn_sub r₁ r₂)
  filter_upwards [lpTensorReal_coe_ae mu (r₁ - r₂) s,
    lpTensorReal_coe_ae mu r₁ s, lpTensorReal_coe_ae mu r₂ s,
    hr,
    Lp.coeFn_sub (lpTensorReal mu r₁ s) (lpTensorReal mu r₂ s)] with p h h₁ h₂ hr hsub
  rw [h, hsub]
  change (r₁ - r₂) p.1 * s p.2 =
    lpTensorReal mu r₁ s p - lpTensorReal mu r₂ s p
  rw [h₁, h₂, hr]
  simp only [Pi.sub_apply]
  ring

theorem lpTensorReal_sub_right
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (r s₁ s₂ : Lp ℝ (2 : ℝ≥0∞) mu) :
    lpTensorReal mu r (s₁ - s₂) =
      lpTensorReal mu r s₁ - lpTensorReal mu r s₂ := by
  apply Lp.ext
  have hsnd : MeasurePreserving Prod.snd (mu.prod mu) mu :=
    measurePreserving_snd
  have hs := hsnd.quasiMeasurePreserving.ae (Lp.coeFn_sub s₁ s₂)
  filter_upwards [lpTensorReal_coe_ae mu r (s₁ - s₂),
    lpTensorReal_coe_ae mu r s₁, lpTensorReal_coe_ae mu r s₂,
    hs,
    Lp.coeFn_sub (lpTensorReal mu r s₁) (lpTensorReal mu r s₂)] with p h h₁ h₂ hs hsub
  rw [h, hsub]
  change r p.1 * (s₁ - s₂) p.2 =
    lpTensorReal mu r s₁ p - lpTensorReal mu r s₂ p
  rw [h₁, h₂, hs]
  simp only [Pi.sub_apply]
  ring

theorem continuous_lpTensorReal_left
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (s : Lp ℝ (2 : ℝ≥0∞) mu) :
    Continuous (fun r : Lp ℝ (2 : ℝ≥0∞) mu => lpTensorReal mu r s) := by
  have hLip : LipschitzWith (⟨‖s‖, norm_nonneg s⟩ : NNReal)
      (fun r : Lp ℝ (2 : ℝ≥0∞) mu => lpTensorReal mu r s) := by
    apply LipschitzWith.of_dist_le_mul
    intro r₁ r₂
    simp only [dist_eq_norm]
    rw [← lpTensorReal_sub_left, norm_lpTensorReal]
    exact (mul_comm _ _).le
  exact hLip.continuous

theorem continuous_lpTensorReal_right
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (r : Lp ℝ (2 : ℝ≥0∞) mu) :
    Continuous (fun s : Lp ℝ (2 : ℝ≥0∞) mu => lpTensorReal mu r s) := by
  have hLip : LipschitzWith (⟨‖r‖, norm_nonneg r⟩ : NNReal)
      (fun s : Lp ℝ (2 : ℝ≥0∞) mu => lpTensorReal mu r s) := by
    apply LipschitzWith.of_dist_le_mul
    intro s₁ s₂
    simp only [dist_eq_norm]
    rw [← lpTensorReal_sub_right, norm_lpTensorReal]
    rfl
  exact hLip.continuous

noncomputable def haarCorrelationBCF
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsLocallyFiniteMeasure m] [m.InnerRegularCompactLTTop]
    [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    BoundedContinuousFunction (Z × Z) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p => inner ℝ ((DomAddAct.mk p.1) +ᵥ u)
        ((DomAddAct.mk p.2) +ᵥ v),
      continuous_haarCorrelation m u v⟩

@[simp] theorem haarCorrelationBCF_apply
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsLocallyFiniteMeasure m] [m.InnerRegularCompactLTTop]
    [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) (p : Z × Z) :
    haarCorrelationBCF m u v p =
      inner ℝ ((DomAddAct.mk p.1) +ᵥ u) ((DomAddAct.mk p.2) +ᵥ v) := rfl

theorem norm_haarCorrelationBCF_le
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsLocallyFiniteMeasure m] [m.InnerRegularCompactLTTop]
    [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    ‖haarCorrelationBCF m u v‖ ≤ ‖u‖ * ‖v‖ := by
  apply (haarCorrelationBCF m u v).norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2
  intro p
  calc
    ‖inner ℝ ((DomAddAct.mk p.1) +ᵥ u) ((DomAddAct.mk p.2) +ᵥ v)‖ ≤
        ‖(DomAddAct.mk p.1) +ᵥ u‖ * ‖(DomAddAct.mk p.2) +ᵥ v‖ :=
      norm_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by simp

noncomputable def haarCorrelationLp
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) : Lp ℝ (2 : ℝ≥0∞) (m.prod m) :=
  BoundedContinuousFunction.toLp 2 (m.prod m) ℝ (haarCorrelationBCF m u v)

theorem haarCorrelationLp_coe_ae
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    (haarCorrelationLp m u v : Z × Z → ℝ) =ᵐ[m.prod m]
      fun p => inner ℝ ((DomAddAct.mk p.1) +ᵥ u)
        ((DomAddAct.mk p.2) +ᵥ v) := by
  exact (haarCorrelationBCF m u v).coeFn_toLp 2 (m.prod m) ℝ

theorem norm_haarCorrelationLp_le
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    ‖haarCorrelationLp m u v‖ ≤ ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ‖BoundedContinuousFunction.toLp 2 (m.prod m) ℝ‖ *
        ‖haarCorrelationBCF m u v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (‖u‖ * ‖v‖) := by
      gcongr
      · have hm : measureUnivNNReal (m.prod m) = 1 := by
          rw [measureUnivNNReal]
          simp
        simpa [hm] using
          (BoundedContinuousFunction.toLp_norm_le
            (μ := m.prod m) (p := (2 : ℝ≥0∞)) (E := ℝ) (𝕜 := ℝ))
      · exact norm_haarCorrelationBCF_le m u v
    _ = _ := one_mul _

theorem haarCorrelationLp_sub_left
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (u₁ u₂ v : Lp ℝ (2 : ℝ≥0∞) m) :
    haarCorrelationLp m (u₁ - u₂) v =
      haarCorrelationLp m u₁ v - haarCorrelationLp m u₂ v := by
  apply Lp.ext
  filter_upwards [haarCorrelationLp_coe_ae m (u₁ - u₂) v,
    haarCorrelationLp_coe_ae m u₁ v, haarCorrelationLp_coe_ae m u₂ v,
    Lp.coeFn_sub (haarCorrelationLp m u₁ v) (haarCorrelationLp m u₂ v)] with p h h₁ h₂ hs
  calc
    haarCorrelationLp m (u₁ - u₂) v p =
        inner ℝ ((DomAddAct.mk p.1) +ᵥ (u₁ - u₂))
          ((DomAddAct.mk p.2) +ᵥ v) := h
    _ = inner ℝ ((DomAddAct.mk p.1) +ᵥ u₁)
          ((DomAddAct.mk p.2) +ᵥ v) -
        inner ℝ ((DomAddAct.mk p.1) +ᵥ u₂)
          ((DomAddAct.mk p.2) +ᵥ v) := by
      rw [DomAddAct.vadd_Lp_sub, inner_sub_left]
    _ = haarCorrelationLp m u₁ v p - haarCorrelationLp m u₂ v p := by
      rw [h₁, h₂]
    _ = (haarCorrelationLp m u₁ v - haarCorrelationLp m u₂ v) p := hs.symm

theorem haarCorrelationLp_sub_right
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (u v₁ v₂ : Lp ℝ (2 : ℝ≥0∞) m) :
    haarCorrelationLp m u (v₁ - v₂) =
      haarCorrelationLp m u v₁ - haarCorrelationLp m u v₂ := by
  apply Lp.ext
  filter_upwards [haarCorrelationLp_coe_ae m u (v₁ - v₂),
    haarCorrelationLp_coe_ae m u v₁, haarCorrelationLp_coe_ae m u v₂,
    Lp.coeFn_sub (haarCorrelationLp m u v₁) (haarCorrelationLp m u v₂)] with p h h₁ h₂ hs
  calc
    haarCorrelationLp m u (v₁ - v₂) p =
        inner ℝ ((DomAddAct.mk p.1) +ᵥ u)
          ((DomAddAct.mk p.2) +ᵥ (v₁ - v₂)) := h
    _ = inner ℝ ((DomAddAct.mk p.1) +ᵥ u)
          ((DomAddAct.mk p.2) +ᵥ v₁) -
        inner ℝ ((DomAddAct.mk p.1) +ᵥ u)
          ((DomAddAct.mk p.2) +ᵥ v₂) := by
      rw [DomAddAct.vadd_Lp_sub, inner_sub_right]
    _ = haarCorrelationLp m u v₁ p - haarCorrelationLp m u v₂ p := by
      rw [h₁, h₂]
    _ = (haarCorrelationLp m u v₁ - haarCorrelationLp m u v₂) p := hs.symm

theorem continuous_haarCorrelationLp_left
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (v : Lp ℝ (2 : ℝ≥0∞) m) :
    Continuous (fun u : Lp ℝ (2 : ℝ≥0∞) m => haarCorrelationLp m u v) := by
  have hLip : LipschitzWith (⟨‖v‖, norm_nonneg v⟩ : NNReal)
      (fun u : Lp ℝ (2 : ℝ≥0∞) m => haarCorrelationLp m u v) := by
    apply LipschitzWith.of_dist_le_mul
    intro u₁ u₂
    simp only [dist_eq_norm]
    calc
      ‖haarCorrelationLp m u₁ v - haarCorrelationLp m u₂ v‖ =
          ‖haarCorrelationLp m (u₁ - u₂) v‖ := by
        rw [haarCorrelationLp_sub_left]
      _ ≤ ‖u₁ - u₂‖ * ‖v‖ := norm_haarCorrelationLp_le m _ _
      _ = (⟨‖v‖, norm_nonneg v⟩ : NNReal) * ‖u₁ - u₂‖ := by
        exact mul_comm _ _
  exact hLip.continuous

theorem continuous_haarCorrelationLp_right
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousVAdd Z Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    (u : Lp ℝ (2 : ℝ≥0∞) m) :
    Continuous (fun v : Lp ℝ (2 : ℝ≥0∞) m => haarCorrelationLp m u v) := by
  have hLip : LipschitzWith (⟨‖u‖, norm_nonneg u⟩ : NNReal)
      (fun v : Lp ℝ (2 : ℝ≥0∞) m => haarCorrelationLp m u v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v₁ v₂
    simp only [dist_eq_norm]
    calc
      ‖haarCorrelationLp m u v₁ - haarCorrelationLp m u v₂‖ =
          ‖haarCorrelationLp m u (v₁ - v₂)‖ := by
        rw [haarCorrelationLp_sub_right]
      _ ≤ ‖u‖ * ‖v₁ - v₂‖ := norm_haarCorrelationLp_le m _ _
      _ = (⟨‖u‖, norm_nonneg u⟩ : NNReal) * ‖v₁ - v₂‖ := rfl
  exact hLip.continuous

theorem inner_toLp_eq_haarDiagonalLimit
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [ContinuousVAdd Z Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m] [Measure.IsAddRightInvariant m]
    (u v : BoundedContinuousFunction Z ℝ) (p : Z × Z) :
    inner ℝ ((DomAddAct.mk p.1) +ᵥ
        BoundedContinuousFunction.toLp 2 m ℝ u)
      ((DomAddAct.mk p.2) +ᵥ
        BoundedContinuousFunction.toLp 2 m ℝ v) =
      haarDiagonalLimit m u v p := by
  rw [inner_domAddAct_eq_integral]
  let d : Z := p.2 - p.1
  let F : Z → ℝ := fun q =>
    (BoundedContinuousFunction.toLp 2 m ℝ u : Z → ℝ) q *
      (BoundedContinuousFunction.toLp 2 m ℝ v : Z → ℝ) (q + d)
  have hchange :
      (∫ z,
        (BoundedContinuousFunction.toLp 2 m ℝ u : Z → ℝ) (p.1 + z) *
          (BoundedContinuousFunction.toLp 2 m ℝ v : Z → ℝ) (p.2 + z) ∂m) =
        ∫ q, F q ∂m := by
    calc
      _ = ∫ z, F (p.1 + z) ∂m := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only [F, d]
          congr 2
          abel
      _ = ∫ q, F q ∂m := by
        simpa using
          ((measurePreserving_add_left m p.1).integral_comp'
            (f := MeasurableEquiv.addLeft p.1) F)
  rw [hchange]
  unfold haarDiagonalLimit haarFiberMean
  apply integral_congr_ae
  have hu := u.coeFn_toLp 2 m ℝ
  have hv := (quasiMeasurePreserving_add_right m d).ae
    (v.coeFn_toLp 2 m ℝ)
  filter_upwards [hu, hv] with q huq hvq
  dsimp only [F, d]
  rw [huq, hvq]
  rfl

theorem haarCorrelationLp_toLp_eq_limit
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [ContinuousVAdd Z Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m] [Measure.IsAddRightInvariant m]
    (u v : BoundedContinuousFunction Z ℝ) :
    haarCorrelationLp m
        (BoundedContinuousFunction.toLp 2 m ℝ u)
        (BoundedContinuousFunction.toLp 2 m ℝ v) =
      (haarDiagonalLimitMemLp m u v).toLp (haarDiagonalLimit m u v) := by
  apply Lp.ext
  filter_upwards [haarCorrelationLp_coe_ae m
      (BoundedContinuousFunction.toLp 2 m ℝ u)
      (BoundedContinuousFunction.toLp 2 m ℝ v),
    (haarDiagonalLimitMemLp m u v).coeFn_toLp] with p hcorr hlim
  rw [hcorr, hlim]
  exact inner_toLp_eq_haarDiagonalLimit m u v p

theorem lpTensorReal_toLp_separated
    {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    (u v : BoundedContinuousFunction Z ℝ) :
    lpTensorReal m
        (BoundedContinuousFunction.toLp 2 m ℝ u)
        (BoundedContinuousFunction.toLp 2 m ℝ v) =
      BoundedContinuousFunction.toLp 2 (m.prod m) ℝ (separatedBCF u v) := by
  apply Lp.ext
  have hu := (measurePreserving_fst (μ := m) (ν := m)).quasiMeasurePreserving.ae
    (u.coeFn_toLp 2 m ℝ)
  have hv := (measurePreserving_snd (μ := m) (ν := m)).quasiMeasurePreserving.ae
    (v.coeFn_toLp 2 m ℝ)
  filter_upwards [lpTensorReal_coe_ae m
      (BoundedContinuousFunction.toLp 2 m ℝ u)
      (BoundedContinuousFunction.toLp 2 m ℝ v),
    (separatedBCF u v).coeFn_toLp 2 (m.prod m) ℝ,
    hu, hv] with p ht hs hu hv
  rw [ht, hs, hu, hv]
  rfl

theorem measurePreserving_haarDiagonalRotation
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m] [Measure.IsAddLeftInvariant m]
    (a : Z) :
    MeasurePreserving (diagonalTransform (fun z : Z => a + z))
      (m.prod m) (m.prod m) := by
  exact (measurePreserving_add_left m a).prod (measurePreserving_add_left m a)

noncomputable def haarDiagonalProjection
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z] [MeasurableAdd₂ Z]
    (m : Measure Z) [IsProbabilityMeasure m] [Measure.IsAddLeftInvariant m]
    (a : Z) :
    Lp ℝ (2 : ℝ≥0∞) (m.prod m) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) (m.prod m) :=
  ((koopmanL2 (diagonalTransform (fun z : Z => a + z)) (m.prod m)
      (measurePreserving_haarDiagonalRotation m a)).eqLocus
    (1 : Lp ℝ (2 : ℝ≥0∞) (m.prod m) →L[ℝ]
      Lp ℝ (2 : ℝ≥0∞) (m.prod m))).starProjection

theorem haarDiagonalProjection_toLp
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [ContinuousVAdd Z Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m] [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z : Z => a + z) m)
    (u v : BoundedContinuousFunction Z ℝ) :
    haarDiagonalProjection m a
        (lpTensorReal m
          (BoundedContinuousFunction.toLp 2 m ℝ u)
          (BoundedContinuousFunction.toLp 2 m ℝ v)) =
      haarCorrelationLp m
        (BoundedContinuousFunction.toLp 2 m ℝ u)
        (BoundedContinuousFunction.toLp 2 m ℝ v) := by
  let D : Z × Z → Z × Z := diagonalTransform (fun z : Z => a + z)
  let hD : MeasurePreserving D (m.prod m) (m.prod m) :=
    measurePreserving_haarDiagonalRotation m a
  let w : Lp ℝ (2 : ℝ≥0∞) (m.prod m) :=
    lpTensorReal m
      (BoundedContinuousFunction.toLp 2 m ℝ u)
      (BoundedContinuousFunction.toLp 2 m ℝ v)
  have hmean := (koopmanL2 D (m.prod m) hD).tendsto_birkhoffAverage_orthogonalProjection
    (norm_koopmanL2_le_one D (m.prod m) hD) w
  have hmean' : Tendsto
      (fun n => birkhoffAverage ℝ (koopmanL2 D (m.prod m) hD) id n w)
      atTop (nhds (haarDiagonalProjection m a w)) := by
    simpa only [D, hD, haarDiagonalProjection, Submodule.starProjection_apply] using hmean
  have havg (n : ℕ) :
      birkhoffAverage ℝ (koopmanL2 D (m.prod m) hD) id n w =
        (haarDiagonalAverageMemLp m a u v n).toLp
          (haarDiagonalAverage a u v n) := by
    have hw : w = BoundedContinuousFunction.toLp 2 (m.prod m) ℝ
        (separatedBCF u v) := lpTensorReal_toLp_separated m u v
    rw [hw]
    apply Lp.ext
    filter_upwards [coe_birkhoffAverage_toLp_ae D (m.prod m) hD
        (separatedBCF u v) n,
      (haarDiagonalAverageMemLp m a u v n).coeFn_toLp] with p h₁ h₂
    rw [h₁, h₂]
    rfl
  have hseq :
      (fun n => birkhoffAverage ℝ (koopmanL2 D (m.prod m) hD) id n w) =
        fun n => (haarDiagonalAverageMemLp m a u v n).toLp
          (haarDiagonalAverage a u v n) := funext havg
  rw [hseq] at hmean'
  have hexp := tendsto_haarDiagonalAverage_toLp m a hrot u v
  have huniq := tendsto_nhds_unique hmean' hexp
  exact huniq.trans (haarCorrelationLp_toLp_eq_limit m u v).symm

theorem haarDiagonalProjection_eq_haarCorrelationLp
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [ContinuousVAdd Z Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m] [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z : Z => a + z) m)
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    haarDiagonalProjection m a (lpTensorReal m u v) =
      haarCorrelationLp m u v := by
  have hdense : DenseRange
      (BoundedContinuousFunction.toLp 2 m ℝ :
        BoundedContinuousFunction Z ℝ → Lp ℝ (2 : ℝ≥0∞) m) :=
    BoundedContinuousFunction.toLp_denseRange ℝ m ℝ (by norm_num)
  have hcontinuousRight (u₀ : Lp ℝ (2 : ℝ≥0∞) m) :
      Continuous (fun v₀ : Lp ℝ (2 : ℝ≥0∞) m =>
        haarDiagonalProjection m a (lpTensorReal m u₀ v₀)) :=
    (haarDiagonalProjection m a).continuous.comp (continuous_lpTensorReal_right m u₀)
  have hcontinuousLeft (v₀ : Lp ℝ (2 : ℝ≥0∞) m) :
      Continuous (fun u₀ : Lp ℝ (2 : ℝ≥0∞) m =>
        haarDiagonalProjection m a (lpTensorReal m u₀ v₀)) :=
    (haarDiagonalProjection m a).continuous.comp (continuous_lpTensorReal_left m v₀)
  have heqLeft (v₀ : BoundedContinuousFunction Z ℝ) :
      (fun u₀ : Lp ℝ (2 : ℝ≥0∞) m =>
        haarDiagonalProjection m a
          (lpTensorReal m u₀ (BoundedContinuousFunction.toLp 2 m ℝ v₀))) =
      fun u₀ => haarCorrelationLp m u₀
        (BoundedContinuousFunction.toLp 2 m ℝ v₀) := by
    apply hdense.equalizer
      (hcontinuousLeft (BoundedContinuousFunction.toLp 2 m ℝ v₀))
      (continuous_haarCorrelationLp_left m
        (BoundedContinuousFunction.toLp 2 m ℝ v₀))
    funext u₀
    exact haarDiagonalProjection_toLp m a hrot u₀ v₀
  have heqRight :
      (fun v₀ : Lp ℝ (2 : ℝ≥0∞) m =>
        haarDiagonalProjection m a (lpTensorReal m u v₀)) =
      fun v₀ => haarCorrelationLp m u v₀ := by
    apply hdense.equalizer (hcontinuousRight u)
      (continuous_haarCorrelationLp_right m u)
    funext v₀
    exact congrFun (heqLeft v₀) u
  exact congrFun heqRight v

theorem tendsto_haarDiagonal_lpTensorReal
    {Z : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [ContinuousVAdd Z Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m] [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z : Z => a + z) m)
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    Tendsto
      (fun n => birkhoffAverage ℝ
        (koopmanL2 (diagonalTransform (fun z : Z => a + z)) (m.prod m)
          (measurePreserving_haarDiagonalRotation m a)) id n
        (lpTensorReal m u v))
      atTop (nhds (haarCorrelationLp m u v)) := by
  let D : Z × Z → Z × Z := diagonalTransform (fun z : Z => a + z)
  let hD : MeasurePreserving D (m.prod m) (m.prod m) :=
    measurePreserving_haarDiagonalRotation m a
  let U := koopmanL2 D (m.prod m) hD
  let S : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) (m.prod m)) :=
    U.eqLocus (1 : Lp ℝ (2 : ℝ≥0∞) (m.prod m) →L[ℝ]
      Lp ℝ (2 : ℝ≥0∞) (m.prod m))
  let w := lpTensorReal m u v
  have hmean := U.tendsto_birkhoffAverage_orthogonalProjection
    (norm_koopmanL2_le_one D (m.prod m) hD) w
  have hproj : ((S.orthogonalProjectionOnto w : S) :
      Lp ℝ (2 : ℝ≥0∞) (m.prod m)) = haarCorrelationLp m u v := by
    rw [S.coe_orthogonalProjectionOnto_apply]
    simpa only [S, U, D, hD, w, haarDiagonalProjection] using
      (haarDiagonalProjection_eq_haarCorrelationLp m a hrot u v)
  rw [hproj] at hmean
  simpa only [U, D, hD, w] using hmean

theorem kernelResidualRealMemLp
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (f : BoundedContinuousFunction X ℝ) :
    MemLp (fun x => f x - kernelExpectation eta f (pi x)) 2
      (Measure.bind m eta) := by
  exact MemLp.of_bound
    (f.continuous.stronglyMeasurable.sub
      ((stronglyMeasurable_kernelExpectation eta f).comp_measurable hpi)).aestronglyMeasurable
    (2 * ‖f‖) (Eventually.of_forall fun x => by
      calc
        ‖f x - kernelExpectation eta f (pi x)‖ ≤
            ‖f x‖ + ‖kernelExpectation eta f (pi x)‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm x)
          (norm_kernelExpectation_le eta f (pi x))
        _ = 2 * ‖f‖ := by ring)

noncomputable def kernelResidualComplexLp
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (f : BoundedContinuousFunction X ℝ) :
    Lp ℂ (2 : ℝ≥0∞) (Measure.bind m eta) :=
  (kernelResidualRealMemLp m eta pi hpi f).ofReal.toLp
    (fun x => ((f x - kernelExpectation eta f (pi x) : ℝ) : ℂ))

theorem kernelResidualComplexLp_coe_ae
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (f : BoundedContinuousFunction X ℝ) :
    (kernelResidualComplexLp m eta pi hpi f : X → ℂ) =ᵐ[Measure.bind m eta]
      fun x => ((f x - kernelExpectation eta f (pi x) : ℝ) : ℂ) := by
  exact (kernelResidualRealMemLp m eta pi hpi f).ofReal.coeFn_toLp

theorem inner_kernelResidualComplexLp_eq_zero
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (f : BoundedContinuousFunction X ℝ)
    (w : Lp ℂ (2 : ℝ≥0∞) (Measure.bind m eta))
    (phi : Z → ℂ)
    (hw : (w : X → ℂ) =ᵐ[Measure.bind m eta] fun x => phi (pi x)) :
    inner ℂ w (kernelResidualComplexLp m eta pi hpi f) = 0 := by
  let r := kernelResidualComplexLp m eta pi hpi f
  let F : X → ℂ := fun x =>
    ((f x - kernelExpectation eta f (pi x) : ℝ) : ℂ) * conj (w x)
  have hres := kernelResidualComplexLp_coe_ae m eta pi hpi f
  have hinnerF : (fun x => inner ℂ (w x) (r x)) =ᵐ[Measure.bind m eta] F := by
    filter_upwards [hres] with x hx
    rw [hx]
    simp only [F, RCLike.inner_apply]
  rw [L2.inner_def, integral_congr_ae hinnerF]
  have hFint : Integrable F (Measure.bind m eta) :=
    (L2.integrable_inner w r).congr hinnerF
  have hFint' : Integrable F ((eta.comp (Kernel.const Unit m)) ()) := by
    rw [← Measure.comp_eq_comp_const_apply]
    exact hFint
  have hcomp := Kernel.integral_comp
    (κ := Kernel.const Unit m) (η := eta) (a := ()) hFint'
  rw [Kernel.const_apply] at hcomp
  rw [Measure.comp_eq_comp_const_apply]
  rw [hcomp]
  have hwcomp : ∀ᵐ x ∂(eta.comp (Kernel.const Unit m)) (),
      w x = phi (pi x) := by
    rw [← Measure.comp_eq_comp_const_apply]
    exact hw
  have hwfiber' : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, w x = phi (pi x) := by
    simpa only [Kernel.const_apply] using
      (Kernel.ae_ae_of_ae_comp hwcomp)
  apply integral_eq_zero_of_ae
  filter_upwards [hfiber, hwfiber'] with z hz hwz
  have hFG : F =ᵐ[eta z] fun x =>
      ((f x - kernelExpectation eta f z : ℝ) : ℂ) * conj (phi z) := by
    filter_upwards [hz, hwz] with x hpix hwx
    simp only [F]
    rw [hwx, hpix]
  rw [integral_congr_ae hFG, integral_mul_const]
  have hfint : Integrable (fun x => f x) (eta z) := f.integrable (eta z)
  have hcint : Integrable (fun _ : X => kernelExpectation eta f z) (eta z) :=
    integrable_const _
  have hreal : (∫ x, f x - kernelExpectation eta f z ∂eta z) = 0 := by
    rw [integral_sub hfint hcint]
    simp [kernelExpectation]
  rw [integral_complex_ofReal, hreal]
  simp

/-- A fiberwise conditional-expectation residual is orthogonal to the whole
Kronecker eigenspace as soon as the chosen normalized eigenvectors factor
through the disintegration coordinate. -/
theorem kernelResidualComplexLp_orthogonal_eigenvectors
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (e : X ≃ᵐ X)
    (he : MeasurePreserving e (Measure.bind m eta) (Measure.bind m eta))
    (herg : Ergodic e (Measure.bind m eta))
    (heigen : ∀ lambda : KoopmanEigenvalueType e (Measure.bind m eta) he,
      ∃ phi : Z → ℂ,
        (normalizedKoopmanEigenvector e (Measure.bind m eta) he lambda : X → ℂ)
          =ᵐ[Measure.bind m eta] fun x => phi (pi x))
    (f : BoundedContinuousFunction X ℝ) :
    ∀ w : Lp ℂ (2 : ℝ≥0∞) (Measure.bind m eta), ∀ lambda : ℂ,
      koopmanL2Complex e (Measure.bind m eta) he w = lambda • w →
        inner ℂ w (kernelResidualComplexLp m eta pi hpi f) = 0 := by
  apply inner_eq_zero_of_orthogonal_chosen_eigenvectors
    e (Measure.bind m eta) herg (kernelResidualComplexLp m eta pi hpi f)
  intro lambda
  obtain ⟨phi, hphi⟩ := heigen lambda
  exact inner_kernelResidualComplexLp_eq_zero
    m eta pi hpi hfiber f
    (normalizedKoopmanEigenvector e (Measure.bind m eta) he lambda) phi hphi

/-- Lift a disintegration fiber to its graph over the base point. -/
noncomputable def graphFiberKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (eta : Kernel Z X) : Kernel Z (X × Z) :=
  eta ×ₖ Kernel.id

instance instIsMarkovKernelGraphFiberKernel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (eta : Kernel Z X) [IsMarkovKernel eta] :
    IsMarkovKernel (graphFiberKernel eta) := by
  unfold graphFiberKernel
  infer_instance

@[simp] theorem graphFiberKernel_apply
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (eta : Kernel Z X) [IsSFiniteKernel eta] (z : Z) :
    graphFiberKernel eta z =
      Measure.map (fun x : X => (x, z)) (eta z) := by
  rw [graphFiberKernel, Kernel.prod_apply, Kernel.id_apply,
    Measure.prod_dirac]

theorem bind_graphFiberKernel_eq_map_swap_compProd
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (m : Measure Z) [SFinite m]
    (eta : Kernel Z X) [IsSFiniteKernel eta] :
    Measure.bind m (graphFiberKernel eta) =
      Measure.map Prod.swap (m ⊗ₘ eta) := by
  ext s hs
  rw [Measure.bind_apply hs (graphFiberKernel eta).aemeasurable,
    Measure.map_apply measurable_swap hs,
    Measure.compProd_apply (measurable_swap hs)]
  congr 1
  funext z
  rw [graphFiberKernel_apply]
  have hmap : Measurable (fun x : X => (x, z)) :=
    measurable_id.prodMk measurable_const
  rw [Measure.map_apply hmap hs]
  rfl

theorem graphFiberKernel_fiber
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [MeasurableEq Z]
    (eta : Kernel Z X) [IsSFiniteKernel eta] (z : Z) :
    ∀ᵐ p ∂graphFiberKernel eta z, p.2 = z := by
  rw [graphFiberKernel_apply]
  have hset : MeasurableSet {p : X × Z | p.2 = z} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hmap : Measurable (fun x : X => (x, z)) :=
    measurable_id.prodMk measurable_const
  exact (ae_map_iff hmap.aemeasurable hset).2
    (Filter.Eventually.of_forall fun _ => rfl)

theorem measurePreserving_kroneckerGraphMap
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    MeasurePreserving (kroneckerGraphMap T mu hT) mu
      (kroneckerGraphMeasure T mu hT) := by
  exact ⟨measurable_kroneckerGraphMap T mu hT, rfl⟩

theorem kroneckerGraphMap_fst_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    ∀ᵐ q ∂kroneckerGraphMeasure T mu hT,
      kroneckerGraphMap T mu hT q.1 = q := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : BorelSpace H := inferInstance
  let : MeasurableEq H := inferInstance
  let pi := kroneckerFactorMap T mu hT
  have hset : MeasurableSet {q : X × H | pi q.1 = q.2} :=
    measurableSet_eq_fun
      ((measurable_kroneckerFactorMap T mu hT).comp measurable_fst)
      measurable_snd
  have hcoord : ∀ᵐ q ∂kroneckerGraphMeasure T mu hT, pi q.1 = q.2 := by
    rw [kroneckerGraphMeasure,
      ae_map_iff (measurable_kroneckerGraphMap T mu hT).aemeasurable hset]
    exact Filter.Eventually.of_forall fun _ => rfl
  filter_upwards [hcoord] with q hq
  exact Prod.ext rfl hq

theorem measurePreserving_fst_kroneckerGraphMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    MeasurePreserving Prod.fst (kroneckerGraphMeasure T mu hT) mu := by
  exact ⟨measurable_fst, map_fst_kroneckerGraphMeasure T mu hT⟩

noncomputable def productRotationMeasurableEquiv
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [AddGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (e : X ≃ᵐ X) (a : Z) : X × Z ≃ᵐ X × Z :=
  e.prodCongr (MeasurableEquiv.addLeft a)

@[simp] theorem productRotationMeasurableEquiv_apply
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [AddGroup Z] [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (e : X ≃ᵐ X) (a : Z) (q : X × Z) :
    productRotationMeasurableEquiv e a q = (e q.1, a + q.2) := rfl

noncomputable def kroneckerGraphMeasurableEquiv
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu) :
    KroneckerGraphSpace e mu he ≃ᵐ KroneckerGraphSpace e mu he := by
  letI : Countable (KoopmanEigenvalueType e mu he.toMeasurePreserving) :=
    (countable_koopmanEigenvalues e mu he.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup e mu he.toMeasurePreserving
  letI : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  letI : BorelSpace H := inferInstance
  letI : MeasurableAdd₂ H := ContinuousAdd.measurableMul₂
  letI : MeasurableNeg H := inferInstance
  exact productRotationMeasurableEquiv e
    (kroneckerSubgroupRotation e mu he)

@[simp] theorem kroneckerGraphMeasurableEquiv_apply
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu) (q : KroneckerGraphSpace e mu he) :
    kroneckerGraphMeasurableEquiv e mu he q =
      (e q.1, kroneckerSubgroupRotation e mu he + q.2) := by
  rfl

theorem measurePreserving_kroneckerGraphMeasurableEquiv
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu) :
    MeasurePreserving
      (kroneckerGraphMeasurableEquiv e mu he)
      (kroneckerGraphMeasure e mu he)
      (kroneckerGraphMeasure e mu he) := by
  have hfun : (kroneckerGraphMeasurableEquiv e mu he :
      KroneckerGraphSpace e mu he → KroneckerGraphSpace e mu he) =
      kroneckerGraphTransform e mu he := by
    funext q
    rfl
  rw [hfun]
  exact (ergodic_kroneckerGraphTransform e mu he).toMeasurePreserving

theorem ergodic_kroneckerGraphMeasurableEquiv
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu) :
    Ergodic
      (kroneckerGraphMeasurableEquiv e mu he)
      (kroneckerGraphMeasure e mu he) := by
  have hfun : (kroneckerGraphMeasurableEquiv e mu he :
      KroneckerGraphSpace e mu he → KroneckerGraphSpace e mu he) =
      kroneckerGraphTransform e mu he := by
    funext q
    rfl
  rw [hfun]
  exact ergodic_kroneckerGraphTransform e mu he

/-- Every eigenfunction on the Kronecker graph is measurable with respect
to the compact coordinate.  This is the characteristic-factor bridge used
for the continuous-spectrum cancellation. -/
theorem kroneckerGraph_eigenvector_factor_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    (w : Lp ℂ (2 : ℝ≥0∞) (kroneckerGraphMeasure e mu he))
    (lambda : ℂ) (hw0 : w ≠ 0)
    (hw : koopmanL2Complex (kroneckerGraphMeasurableEquiv e mu he)
      (kroneckerGraphMeasure e mu he)
      (measurePreserving_kroneckerGraphMeasurableEquiv e mu he) w =
        lambda • w) :
    ∃ phi : KroneckerSubgroup e mu he.toMeasurePreserving → ℂ,
      Measurable phi ∧
      (w : KroneckerGraphSpace e mu he → ℂ) =ᵐ[kroneckerGraphMeasure e mu he]
        fun q => phi q.2 := by
  let E := kroneckerGraphMeasurableEquiv e mu he
  let nu := kroneckerGraphMeasure e mu he
  let G := kroneckerGraphMap e mu he
  let hG := measurePreserving_kroneckerGraphMap e mu he
  let hE := measurePreserving_kroneckerGraphMeasurableEquiv e mu he
  let v : Lp ℂ (2 : ℝ≥0∞) mu := Lp.compMeasurePreserving G hG w
  have hv0 : v ≠ 0 := by
    rw [← norm_ne_zero_iff, show ‖v‖ = ‖w‖ by
      exact Lp.norm_compMeasurePreserving w hG]
    exact norm_ne_zero_iff.mpr hw0
  have hv : koopmanL2Complex e mu he.toMeasurePreserving v = lambda • v := by
    rw [Lp.ext_iff]
    have hvcoe : (v : X → ℂ) =ᵐ[mu] fun x => w (G x) :=
      Lp.coeFn_compMeasurePreserving w hG
    have hvcoe_e : ∀ᵐ x ∂mu, v (e x) = w (G (e x)) :=
      he.toMeasurePreserving.quasiMeasurePreserving.ae hvcoe
    have hwe : (fun q => w (E q)) =ᵐ[nu] fun q => lambda * w q :=
      koopman_eigen_ae E nu hE hw
    have hweG : ∀ᵐ x ∂mu, w (E (G x)) = lambda * w (G x) :=
      hG.quasiMeasurePreserving.ae hwe
    have hsemi : ∀ᵐ x ∂mu, G (e x) = E (G x) := by
      filter_upwards [kroneckerGraphMap_semiconj_ae e mu he] with x hx
      change G (e x) = kroneckerGraphTransform e mu he (G x) at hx
      exact hx
    filter_upwards [Lp.coeFn_compMeasurePreserving v he.toMeasurePreserving,
      Lp.coeFn_smul lambda v, hvcoe, hvcoe_e, hweG, hsemi] with
        x hkoop hsmul hvx hvex hwx hsemix
    calc
      (koopmanL2Complex e mu he.toMeasurePreserving v) x = v (e x) := hkoop
      _ = w (G (e x)) := hvex
      _ = w (E (G x)) := congrArg w hsemix
      _ = lambda * w (G x) := hwx
      _ = lambda * v x := congrArg (fun z => lambda * z) hvx.symm
      _ = (lambda • v) x := hsmul.symm
  let lambdaBase : KoopmanEigenvalueType e mu he.toMeasurePreserving :=
    ⟨lambda, v, hv0, hv⟩
  obtain ⟨phiBase, hphiBase, hfactor⟩ :=
    normalizedKoopmanEigenvector_factor_ae e mu he lambdaBase
  obtain ⟨c, hvc⟩ := eq_smul_of_same_koopman_eigenvalue e mu he hv
    (by
      rw [← norm_ne_zero_iff,
        norm_normalizedKoopmanEigenvector]
      norm_num)
    (normalizedKoopmanEigenvector_eigen e mu he.toMeasurePreserving lambdaBase)
  let phi : KroneckerSubgroup e mu he.toMeasurePreserving → ℂ :=
    fun z => c * phiBase z
  have hphi : Measurable phi := measurable_const.mul hphiBase
  refine ⟨phi, hphi, ?_⟩
  have hvcAe : (v : X → ℂ) =ᵐ[mu]
      fun x => c * phiBase (kroneckerFactorMap e mu he x) := by
    have hlp := Lp.ext_iff.mp hvc
    filter_upwards [hlp, Lp.coeFn_smul c
      (normalizedKoopmanEigenvector e mu he.toMeasurePreserving lambdaBase),
      hfactor] with x hx hsmulx hfactorx
    rw [hx, hsmulx]
    change c *
      (normalizedKoopmanEigenvector e mu he.toMeasurePreserving lambdaBase : X → ℂ) x =
        c * phiBase (kroneckerFactorMap e mu he x)
    rw [hfactorx]
  have hvGraph : ∀ᵐ q ∂nu,
      v q.1 = c * phiBase (kroneckerFactorMap e mu he q.1) :=
    (measurePreserving_fst_kroneckerGraphMeasure e mu he).quasiMeasurePreserving.ae
      hvcAe
  have hvcoe : (v : X → ℂ) =ᵐ[mu] fun x => w (G x) :=
    Lp.coeFn_compMeasurePreserving w hG
  have hvcoeGraph : ∀ᵐ q ∂nu, v q.1 = w (G q.1) :=
    (measurePreserving_fst_kroneckerGraphMeasure e mu he).quasiMeasurePreserving.ae
      hvcoe
  have hInv := kroneckerGraphMap_fst_ae e mu he
  filter_upwards [hvGraph, hvcoeGraph, hInv] with q hvq hcoeq hq
  have hcoord : kroneckerFactorMap e mu he q.1 = q.2 :=
    congrArg Prod.snd hq
  calc
    w q = w (G q.1) := congrArg w hq.symm
    _ = v q.1 := hcoeq.symm
    _ = c * phiBase (kroneckerFactorMap e mu he q.1) := hvq
    _ = phi q.2 := by rw [hcoord]

noncomputable def complexifyLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) :
    Lp ℝ (2 : ℝ≥0∞) mu →L[ℝ] Lp ℂ (2 : ℝ≥0∞) mu :=
  Complex.ofRealCLM.compLpL 2 mu

noncomputable def realPartLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) :
    Lp ℂ (2 : ℝ≥0∞) mu →L[ℝ] Lp ℝ (2 : ℝ≥0∞) mu :=
  Complex.reCLM.compLpL 2 mu

theorem complexifyLp_coe_ae
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (f : Lp ℝ (2 : ℝ≥0∞) mu) :
    (complexifyLp mu f : X → ℂ) =ᵐ[mu] fun x => (f x : ℂ) := by
  simpa only [complexifyLp, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.coeFn_compLpL f

theorem realPartLp_coe_ae
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (f : Lp ℂ (2 : ℝ≥0∞) mu) :
    (realPartLp mu f : X → ℝ) =ᵐ[mu] fun x => (f x).re := by
  simpa only [realPartLp, Complex.reCLM_apply] using
    Complex.reCLM.coeFn_compLpL f

@[simp] theorem realPartLp_zero
    {X : Type*} [MeasurableSpace X] (mu : Measure X) :
    realPartLp mu (0 : Lp ℂ (2 : ℝ≥0∞) mu) = 0 := by
  exact (realPartLp mu).map_zero

theorem realPartLp_koopman
    {X : Type*} [MeasurableSpace X] (e : X → X)
    (mu : Measure X) (he : MeasurePreserving e mu mu)
    (f : Lp ℂ (2 : ℝ≥0∞) mu) :
    realPartLp mu (koopmanL2Complex e mu he f) =
      koopmanL2 e mu he (realPartLp mu f) := by
  apply Lp.ext
  have hre := realPartLp_coe_ae mu f
  filter_upwards [realPartLp_coe_ae mu (koopmanL2Complex e mu he f),
    Lp.coeFn_compMeasurePreserving f he,
    Lp.coeFn_compMeasurePreserving (realPartLp mu f) he,
    he.quasiMeasurePreserving.ae hre] with x hl hc hr hrex
  have hc' : (koopmanL2Complex e mu he f : X → ℂ) x = f (e x) := by
    change (Lp.compMeasurePreserving e he f : X → ℂ) x = f (e x)
    exact hc
  have hr' : (koopmanL2 e mu he (realPartLp mu f) : X → ℝ) x =
      realPartLp mu f (e x) := by
    change (Lp.compMeasurePreserving e he (realPartLp mu f) : X → ℝ) x =
      realPartLp mu f (e x)
    exact hr
  calc
    (realPartLp mu (koopmanL2Complex e mu he f) : X → ℝ) x =
        (koopmanL2Complex e mu he f x).re := hl
    _ = (f (e x)).re := congrArg Complex.re hc'
    _ = realPartLp mu f (e x) := hrex.symm
    _ = (koopmanL2 e mu he (realPartLp mu f) : X → ℝ) x := hr'.symm

theorem realPartLp_koopman_iterate
    {X : Type*} [MeasurableSpace X] (e : X → X)
    (mu : Measure X) (he : MeasurePreserving e mu mu)
    (f : Lp ℂ (2 : ℝ≥0∞) mu) (n : ℕ) :
    realPartLp mu (((koopmanL2Complex e mu he) ^ n) f) =
      ((koopmanL2 e mu he) ^ n) (realPartLp mu f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change realPartLp mu
          (((koopmanL2Complex e mu he) ^ n)
            (koopmanL2Complex e mu he f)) =
        ((koopmanL2 e mu he) ^ n)
          (koopmanL2 e mu he (realPartLp mu f))
      rw [ih, realPartLp_koopman]

theorem realPartLp_birkhoffAverage_koopman
    {X : Type*} [MeasurableSpace X] (e : X → X)
    (mu : Measure X) (he : MeasurePreserving e mu mu)
    (f : Lp ℂ (2 : ℝ≥0∞) mu) (n : ℕ) :
    realPartLp mu
        (birkhoffAverage ℂ (koopmanL2Complex e mu he) id n f) =
      birkhoffAverage ℝ (koopmanL2 e mu he) id n (realPartLp mu f) := by
  rw [map_birkhoffAverage ℂ ℝ (realPartLp mu)
    (koopmanL2Complex e mu he) id n f]
  unfold birkhoffAverage birkhoffSum
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hiter : ∀ j : ℕ,
      realPartLp mu (((koopmanL2Complex e mu he)^[j]) f) =
        ((koopmanL2 e mu he)^[j]) (realPartLp mu f) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          realPartLp_koopman, ih]
  exact hiter i

theorem lpTensor_complexifyLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (r s : Lp ℝ (2 : ℝ≥0∞) mu) :
    lpTensor mu (complexifyLp mu r) (complexifyLp mu s) =
      complexifyLp (mu.prod mu) (lpTensorReal mu r s) := by
  apply Lp.ext
  have hr := (measurePreserving_fst (μ := mu) (ν := mu)).quasiMeasurePreserving.ae
    (complexifyLp_coe_ae mu r)
  have hs := (measurePreserving_snd (μ := mu) (ν := mu)).quasiMeasurePreserving.ae
    (complexifyLp_coe_ae mu s)
  filter_upwards [lpTensor_coe_ae mu (complexifyLp mu r) (complexifyLp mu s),
    complexifyLp_coe_ae (mu.prod mu) (lpTensorReal mu r s),
    lpTensorReal_coe_ae mu r s, hr, hs] with p ht hc htr hrp hsp
  rw [ht, hc, htr, hrp, hsp]
  norm_cast

theorem realPartLp_complexifyLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (f : Lp ℝ (2 : ℝ≥0∞) mu) :
    realPartLp mu (complexifyLp mu f) = f := by
  apply Lp.ext
  filter_upwards [realPartLp_coe_ae mu (complexifyLp mu f),
    complexifyLp_coe_ae mu f] with x hr hc
  rw [hr, hc]
  simp

noncomputable def kernelResidualRealLp
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (f : BoundedContinuousFunction X ℝ) :
    Lp ℝ (2 : ℝ≥0∞) (Measure.bind m eta) :=
  (kernelResidualRealMemLp m eta pi hpi f).toLp
    (fun x => f x - kernelExpectation eta f (pi x))

theorem kernelResidualRealLp_coe_ae
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (f : BoundedContinuousFunction X ℝ) :
    (kernelResidualRealLp m eta pi hpi f : X → ℝ) =ᵐ[Measure.bind m eta]
      fun x => f x - kernelExpectation eta f (pi x) := by
  exact (kernelResidualRealMemLp m eta pi hpi f).coeFn_toLp

theorem kernelResidualComplexLp_eq_complexify
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (f : BoundedContinuousFunction X ℝ) :
    kernelResidualComplexLp m eta pi hpi f =
      complexifyLp (Measure.bind m eta)
        (kernelResidualRealLp m eta pi hpi f) := by
  apply Lp.ext
  filter_upwards [kernelResidualComplexLp_coe_ae m eta pi hpi f,
    complexifyLp_coe_ae (Measure.bind m eta)
      (kernelResidualRealLp m eta pi hpi f),
    kernelResidualRealLp_coe_ae m eta pi hpi f] with x hc hcr hr
  rw [hc, hcr, hr]

theorem tendsto_kernelResidual_lpTensorReal_average_zero
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (e : X ≃ᵐ X)
    (he : MeasurePreserving e (Measure.bind m eta) (Measure.bind m eta))
    (herg : Ergodic e (Measure.bind m eta))
    (heigen : ∀ lambda : KoopmanEigenvalueType e (Measure.bind m eta) he,
      ∃ phi : Z → ℂ,
        (normalizedKoopmanEigenvector e (Measure.bind m eta) he lambda : X → ℂ)
          =ᵐ[Measure.bind m eta] fun x => phi (pi x))
    (f : BoundedContinuousFunction X ℝ)
    (s : Lp ℝ (2 : ℝ≥0∞) (Measure.bind m eta)) :
    Tendsto (fun n => birkhoffAverage ℝ
      (koopmanL2 (Prod.map e e)
        ((Measure.bind m eta).prod (Measure.bind m eta)) (he.prod he))
      id (n + 1)
      (lpTensorReal (Measure.bind m eta)
        (kernelResidualRealLp m eta pi hpi f) s))
      atTop (nhds 0) := by
  let nu := Measure.bind m eta
  let rR := kernelResidualRealLp m eta pi hpi f
  let rC := kernelResidualComplexLp m eta pi hpi f
  let sC := complexifyLp nu s
  have horth : ∀ w : Lp ℂ (2 : ℝ≥0∞) nu, ∀ lambda : ℂ,
      koopmanL2Complex e nu he w = lambda • w → inner ℂ w rC = 0 := by
    exact kernelResidualComplexLp_orthogonal_eigenvectors
      m eta pi hpi hfiber e he herg heigen f
  have hc := tendsto_lpTensor_average_zero e nu he rC sC horth
  have hrC : rC = complexifyLp nu rR := by
    exact kernelResidualComplexLp_eq_complexify m eta pi hpi f
  have htensor : lpTensor nu rC sC =
      complexifyLp (nu.prod nu) (lpTensorReal nu rR s) := by
    rw [hrC]
    exact lpTensor_complexifyLp nu rR s
  rw [htensor] at hc
  have hcont : Tendsto (realPartLp (nu.prod nu)) (nhds 0)
      (nhds (realPartLp (nu.prod nu) 0)) :=
    (realPartLp (nu.prod nu)).continuous.continuousAt
  have hmapped := hcont.comp hc
  have hseq :
      (realPartLp (nu.prod nu) ∘ fun n => birkhoffAverage ℂ
        (koopmanL2Complex (Prod.map e e) (nu.prod nu) (he.prod he)) id (n + 1)
        (complexifyLp (nu.prod nu) (lpTensorReal nu rR s))) =
      fun n => birkhoffAverage ℝ
        (koopmanL2 (Prod.map e e) (nu.prod nu) (he.prod he)) id (n + 1)
        (lpTensorReal nu rR s) := by
    funext n
    rw [Function.comp_apply,
      realPartLp_birkhoffAverage_koopman,
      realPartLp_complexifyLp]
  rw [hseq, realPartLp_zero] at hmapped
  simpa only [nu, rR] using hmapped

theorem compProd_kroneckerFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    kroneckerFactorMeasure T mu hT ⊗ₘ kroneckerFiberKernel T mu hT =
      Measure.map (fun x => (kroneckerFactorMap T mu hT x, x)) mu := by
  simpa only [kroneckerFiberKernel, kroneckerFactorMeasure, id_eq] using
    (compProd_map_condDistrib (μ := mu) (X := kroneckerFactorMap T mu hT)
      (Y := id) (measurable_kroneckerFactorMap T mu hT).aemeasurable aemeasurable_id)

noncomputable def kroneckerGraphFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Kernel (KroneckerSubgroup T mu hT.toMeasurePreserving)
      (KroneckerGraphSpace T mu hT) :=
  graphFiberKernel (kroneckerFiberKernel T mu hT)

instance instIsMarkovKernelKroneckerGraphFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    IsMarkovKernel (kroneckerGraphFiberKernel T mu hT) := by
  unfold kroneckerGraphFiberKernel
  infer_instance

theorem bind_kroneckerGraphFiberKernel
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    Measure.bind (kroneckerFactorMeasure T mu hT)
      (kroneckerGraphFiberKernel T mu hT) =
        kroneckerGraphMeasure T mu hT := by
  rw [kroneckerGraphFiberKernel,
    bind_graphFiberKernel_eq_map_swap_compProd,
    compProd_kroneckerFiberKernel, kroneckerGraphMeasure,
    Measure.map_map]
  · congr 1
  · exact measurable_swap
  · exact (measurable_kroneckerFactorMap T mu hT).prodMk measurable_id

theorem kroneckerGraphFiberKernel_fiber
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    ∀ᵐ z ∂kroneckerFactorMeasure T mu hT,
      ∀ᵐ q ∂kroneckerGraphFiberKernel T mu hT z, q.2 = z := by
  let : Countable (KoopmanEigenvalueType T mu hT.toMeasurePreserving) :=
    (countable_koopmanEigenvalues T mu hT.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup T mu hT.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : BorelSpace H := inferInstance
  let : MeasurableEq H := inferInstance
  exact Filter.Eventually.of_forall fun z => by
    exact graphFiberKernel_fiber (kroneckerFiberKernel T mu hT) z

noncomputable abbrev kroneckerGraphBindMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) : Measure (KroneckerGraphSpace T mu hT) :=
  Measure.bind (kroneckerFactorMeasure T mu hT)
    (kroneckerGraphFiberKernel T mu hT)

theorem measurePreserving_kroneckerGraphBind
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu) :
    MeasurePreserving (kroneckerGraphMeasurableEquiv e mu he)
      (kroneckerGraphBindMeasure e mu he)
      (kroneckerGraphBindMeasure e mu he) := by
  rw [kroneckerGraphBindMeasure, bind_kroneckerGraphFiberKernel]
  exact measurePreserving_kroneckerGraphMeasurableEquiv e mu he

theorem tendsto_kroneckerGraphResidual_lpTensorReal_average_zero
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [BorelSpace (KroneckerGraphSpace e mu he)]
    (f : BoundedContinuousFunction (KroneckerGraphSpace e mu he) ℝ)
    (s : Lp ℝ (2 : ℝ≥0∞) (kroneckerGraphBindMeasure e mu he)) :
    Tendsto (fun n => birkhoffAverage ℝ
      (koopmanL2
        (Prod.map (kroneckerGraphMeasurableEquiv e mu he)
          (kroneckerGraphMeasurableEquiv e mu he))
        ((kroneckerGraphBindMeasure e mu he).prod
          (kroneckerGraphBindMeasure e mu he))
        ((measurePreserving_kroneckerGraphBind e mu he).prod
          (measurePreserving_kroneckerGraphBind e mu he)))
      id (n + 1)
      (lpTensorReal
        (kroneckerGraphBindMeasure e mu he)
        (kernelResidualRealLp (kroneckerFactorMeasure e mu he)
          (kroneckerGraphFiberKernel e mu he) Prod.snd measurable_snd f) s))
      atTop (nhds 0) := by
  let m := kroneckerFactorMeasure e mu he
  let eta := kroneckerGraphFiberKernel e mu he
  let E := kroneckerGraphMeasurableEquiv e mu he
  let nu := Measure.bind m eta
  have hbind : Measure.bind m eta = kroneckerGraphMeasure e mu he := by
    simpa only [m, eta] using bind_kroneckerGraphFiberKernel e mu he
  have hE : MeasurePreserving E nu nu := by
    change MeasurePreserving E (Measure.bind m eta) (Measure.bind m eta)
    rw [hbind]
    exact measurePreserving_kroneckerGraphMeasurableEquiv e mu he
  have hErg : Ergodic E nu := by
    change Ergodic E (Measure.bind m eta)
    rw [hbind]
    exact ergodic_kroneckerGraphMeasurableEquiv e mu he
  let EigenFactors := fun rho : Measure (KroneckerGraphSpace e mu he) =>
    ∀ hR : MeasurePreserving E rho rho,
      ∀ lambda : KoopmanEigenvalueType E rho hR,
        ∃ phi : KroneckerSubgroup e mu he.toMeasurePreserving → ℂ,
          (normalizedKoopmanEigenvector E rho hR lambda :
            KroneckerGraphSpace e mu he → ℂ) =ᵐ[rho] fun q => phi q.2
  have heigenGraph : EigenFactors (kroneckerGraphMeasure e mu he) := by
    intro hR lambda
    have hw0 : normalizedKoopmanEigenvector E
        (kroneckerGraphMeasure e mu he) hR lambda ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]
      norm_num
    have hw := normalizedKoopmanEigenvector_eigen E
      (kroneckerGraphMeasure e mu he) hR lambda
    obtain ⟨phi, hphi, hfac⟩ :=
      kroneckerGraph_eigenvector_factor_ae e mu he
        (normalizedKoopmanEigenvector E (kroneckerGraphMeasure e mu he)
          hR lambda)
        (lambda : ℂ) hw0 hw
    exact ⟨phi, hfac⟩
  have heigenNu : EigenFactors nu := by
    dsimp only [nu]
    rw [hbind]
    exact heigenGraph
  have heigen : ∀ lambda : KoopmanEigenvalueType E nu hE,
      ∃ phi : KroneckerSubgroup e mu he.toMeasurePreserving → ℂ,
        (normalizedKoopmanEigenvector E nu hE lambda :
          KroneckerGraphSpace e mu he → ℂ) =ᵐ[nu] fun q => phi q.2 := by
    exact heigenNu hE
  have hzero := tendsto_kernelResidual_lpTensorReal_average_zero
    m eta Prod.snd measurable_snd
    (kroneckerGraphFiberKernel_fiber e mu he)
    E hE hErg heigen f s
  simpa only [m, eta, E, nu] using hzero

theorem tendsto_lpTensor_average_zero_right
    {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X)
    (mu : Measure X) [IsProbabilityMeasure mu]
    (he : MeasurePreserving e mu mu)
    (r s : Lp ℂ (2 : ℝ≥0∞) mu)
    (hs : ∀ w : Lp ℂ (2 : ℝ≥0∞) mu, ∀ lambda : ℂ,
      koopmanL2Complex e mu he w = lambda • w → inner ℂ w s = 0) :
    Tendsto (fun n => birkhoffAverage ℂ
      (koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he)) id (n + 1)
      (lpTensor mu r s)) atTop (nhds 0) := by
  let u := koopmanUnitary e mu he
  have hssq := Spectral.unitary_correlation_mean_square_tendsto_zero u s (by
    intro lambda w hw
    apply hs w lambda
    simpa [u] using hw)
  apply Spectral.tendsto_birkhoffAverage_zero_of_correlation_dominated
    (koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he))
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simpa only [one_mul] using
        le_of_eq (norm_koopmanL2Complex (Prod.map e e) (mu.prod mu) (he.prod he) v))
    (lpTensor mu r s) (fun k => ‖inner ℂ s
      (((koopmanL2Complex e mu he) ^ k) s)‖) (fun _ => norm_nonneg _) hssq
    (‖r‖ ^ 2) (sq_nonneg _)
  intro k
  rw [inner_lpTensor_koopman_pow e mu he r s k, norm_mul]
  gcongr
  calc
    ‖inner ℂ r (((koopmanL2Complex e mu he) ^ k) r)‖ ≤
        ‖r‖ * ‖((koopmanL2Complex e mu he) ^ k) r‖ :=
      norm_inner_le_norm r (((koopmanL2Complex e mu he) ^ k) r)
    _ = ‖r‖ ^ 2 := by
      rw [show (((koopmanL2Complex e mu he) ^ k) r) =
        Lp.compMeasurePreserving e^[k] (he.iterate k) r by
          rw [Spectral.pow_continuousLinearMap_apply]
          change ((Lp.compMeasurePreserving e he)^[k]) r = _
          rw [Lp.compMeasurePreserving_iterate],
        Lp.norm_compMeasurePreserving]
      exact (pow_two ‖r‖).symm

theorem tendsto_kernelResidual_lpTensorReal_average_zero_right
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    (eta : Kernel Z X) [IsMarkovKernel eta]
    (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (e : X ≃ᵐ X)
    (he : MeasurePreserving e (Measure.bind m eta) (Measure.bind m eta))
    (herg : Ergodic e (Measure.bind m eta))
    (heigen : ∀ lambda : KoopmanEigenvalueType e (Measure.bind m eta) he,
      ∃ phi : Z → ℂ,
        (normalizedKoopmanEigenvector e (Measure.bind m eta) he lambda : X → ℂ)
          =ᵐ[Measure.bind m eta] fun x => phi (pi x))
    (r : Lp ℝ (2 : ℝ≥0∞) (Measure.bind m eta))
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n => birkhoffAverage ℝ
      (koopmanL2 (Prod.map e e)
        ((Measure.bind m eta).prod (Measure.bind m eta)) (he.prod he))
      id (n + 1)
      (lpTensorReal (Measure.bind m eta) r
        (kernelResidualRealLp m eta pi hpi f)))
      atTop (nhds 0) := by
  let nu := Measure.bind m eta
  let rC := complexifyLp nu r
  let sR := kernelResidualRealLp m eta pi hpi f
  let sC := kernelResidualComplexLp m eta pi hpi f
  have horth : ∀ w : Lp ℂ (2 : ℝ≥0∞) nu, ∀ lambda : ℂ,
      koopmanL2Complex e nu he w = lambda • w → inner ℂ w sC = 0 := by
    exact kernelResidualComplexLp_orthogonal_eigenvectors
      m eta pi hpi hfiber e he herg heigen f
  have hc := tendsto_lpTensor_average_zero_right e nu he rC sC horth
  have hsC : sC = complexifyLp nu sR := by
    exact kernelResidualComplexLp_eq_complexify m eta pi hpi f
  have htensor : lpTensor nu rC sC =
      complexifyLp (nu.prod nu) (lpTensorReal nu r sR) := by
    rw [hsC]
    exact lpTensor_complexifyLp nu r sR
  rw [htensor] at hc
  have hcont : Tendsto (realPartLp (nu.prod nu)) (nhds 0)
      (nhds (realPartLp (nu.prod nu) 0)) :=
    (realPartLp (nu.prod nu)).continuous.continuousAt
  have hmapped := hcont.comp hc
  have hseq :
      (realPartLp (nu.prod nu) ∘ fun n => birkhoffAverage ℂ
        (koopmanL2Complex (Prod.map e e) (nu.prod nu) (he.prod he)) id (n + 1)
        (complexifyLp (nu.prod nu) (lpTensorReal nu r sR))) =
      fun n => birkhoffAverage ℝ
        (koopmanL2 (Prod.map e e) (nu.prod nu) (he.prod he)) id (n + 1)
        (lpTensorReal nu r sR) := by
    funext n
    rw [Function.comp_apply, realPartLp_birkhoffAverage_koopman,
      realPartLp_complexifyLp]
  rw [hseq, realPartLp_zero] at hmapped
  simpa only [nu, sR] using hmapped

theorem ergodic_kroneckerGraphBind
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu) :
    Ergodic (kroneckerGraphMeasurableEquiv e mu he)
      (kroneckerGraphBindMeasure e mu he) := by
  rw [kroneckerGraphBindMeasure, bind_kroneckerGraphFiberKernel]
  exact ergodic_kroneckerGraphMeasurableEquiv e mu he

theorem kroneckerGraphBind_eigenvector_factor_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    (lambda : KoopmanEigenvalueType (kroneckerGraphMeasurableEquiv e mu he)
      (kroneckerGraphBindMeasure e mu he)
      (measurePreserving_kroneckerGraphBind e mu he)) :
    ∃ phi : KroneckerSubgroup e mu he.toMeasurePreserving → ℂ,
      (normalizedKoopmanEigenvector (kroneckerGraphMeasurableEquiv e mu he)
        (kroneckerGraphBindMeasure e mu he)
        (measurePreserving_kroneckerGraphBind e mu he) lambda :
        KroneckerGraphSpace e mu he → ℂ) =ᵐ[kroneckerGraphBindMeasure e mu he]
          fun q => phi q.2 := by
  let E := kroneckerGraphMeasurableEquiv e mu he
  let nu := kroneckerGraphBindMeasure e mu he
  let hE := measurePreserving_kroneckerGraphBind e mu he
  let EigenFactors := fun rho : Measure (KroneckerGraphSpace e mu he) =>
    ∀ hR : MeasurePreserving E rho rho,
      ∀ lam : KoopmanEigenvalueType E rho hR,
        ∃ phi : KroneckerSubgroup e mu he.toMeasurePreserving → ℂ,
          (normalizedKoopmanEigenvector E rho hR lam :
            KroneckerGraphSpace e mu he → ℂ) =ᵐ[rho] fun q => phi q.2
  have hgraph : EigenFactors (kroneckerGraphMeasure e mu he) := by
    intro hR lam
    have hw0 : normalizedKoopmanEigenvector E
        (kroneckerGraphMeasure e mu he) hR lam ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_normalizedKoopmanEigenvector]
      norm_num
    have hw := normalizedKoopmanEigenvector_eigen E
      (kroneckerGraphMeasure e mu he) hR lam
    obtain ⟨phi, hphi, hfac⟩ := kroneckerGraph_eigenvector_factor_ae e mu he
      (normalizedKoopmanEigenvector E (kroneckerGraphMeasure e mu he) hR lam)
      (lam : ℂ) hw0 hw
    exact ⟨phi, hfac⟩
  have hbind : nu = kroneckerGraphMeasure e mu he := by
    exact bind_kroneckerGraphFiberKernel e mu he
  have hnu : EigenFactors nu := by
    rw [hbind]
    exact hgraph
  exact hnu hE lambda

theorem tendsto_kroneckerGraphResidual_lpTensorReal_average_zero_right
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [BorelSpace (KroneckerGraphSpace e mu he)]
    (r : Lp ℝ (2 : ℝ≥0∞) (kroneckerGraphBindMeasure e mu he))
    (f : BoundedContinuousFunction (KroneckerGraphSpace e mu he) ℝ) :
    Tendsto (fun n => birkhoffAverage ℝ
      (koopmanL2
        (Prod.map (kroneckerGraphMeasurableEquiv e mu he)
          (kroneckerGraphMeasurableEquiv e mu he))
        ((kroneckerGraphBindMeasure e mu he).prod
          (kroneckerGraphBindMeasure e mu he))
        ((measurePreserving_kroneckerGraphBind e mu he).prod
          (measurePreserving_kroneckerGraphBind e mu he)))
      id (n + 1)
      (lpTensorReal (kroneckerGraphBindMeasure e mu he) r
        (kernelResidualRealLp (kroneckerFactorMeasure e mu he)
          (kroneckerGraphFiberKernel e mu he) Prod.snd measurable_snd f)))
      atTop (nhds 0) := by
  exact tendsto_kernelResidual_lpTensorReal_average_zero_right
    (kroneckerFactorMeasure e mu he) (kroneckerGraphFiberKernel e mu he)
    Prod.snd measurable_snd (kroneckerGraphFiberKernel_fiber e mu he)
    (kroneckerGraphMeasurableEquiv e mu he)
    (measurePreserving_kroneckerGraphBind e mu he)
    (ergodic_kroneckerGraphBind e mu he)
    (kroneckerGraphBind_eigenvector_factor_ae e mu he) r f

noncomputable def pullbackLp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (pi : X → Y) (nu : Measure X) (m : Measure Y)
    (hpi : MeasurePreserving pi nu m) :
    Lp ℝ (2 : ℝ≥0∞) m →L[ℝ] Lp ℝ (2 : ℝ≥0∞) nu :=
  (Lp.compMeasurePreservingₗᵢ (p := (2 : ℝ≥0∞)) ℝ pi hpi).toContinuousLinearMap

theorem pullbackLp_coe_ae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (pi : X → Y) (nu : Measure X) (m : Measure Y)
    (hpi : MeasurePreserving pi nu m) (f : Lp ℝ (2 : ℝ≥0∞) m) :
    (pullbackLp pi nu m hpi f : X → ℝ) =ᵐ[nu] fun x => f (pi x) := by
  exact Lp.coeFn_compMeasurePreserving f hpi

theorem pullbackLp_koopman
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (pi : X → Y) (nu : Measure X) (m : Measure Y)
    (hpi : MeasurePreserving pi nu m)
    (T : X → X) (S : Y → Y)
    (hT : MeasurePreserving T nu nu) (hS : MeasurePreserving S m m)
    (hcomm : ∀ x, pi (T x) = S (pi x))
    (f : Lp ℝ (2 : ℝ≥0∞) m) :
    pullbackLp pi nu m hpi (koopmanL2 S m hS f) =
      koopmanL2 T nu hT (pullbackLp pi nu m hpi f) := by
  apply Lp.ext
  have hcoe := pullbackLp_coe_ae pi nu m hpi f
  filter_upwards [pullbackLp_coe_ae pi nu m hpi (koopmanL2 S m hS f),
    hpi.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hS),
    Lp.coeFn_compMeasurePreserving (pullbackLp pi nu m hpi f) hT,
    hT.quasiMeasurePreserving.ae hcoe] with x hl hs hr hfx
  have hs' : (koopmanL2 S m hS f : Y → ℝ) (pi x) = f (S (pi x)) := by
    change (Lp.compMeasurePreserving S hS f : Y → ℝ) (pi x) = f (S (pi x))
    exact hs
  have hr' : (koopmanL2 T nu hT (pullbackLp pi nu m hpi f) : X → ℝ) x =
      pullbackLp pi nu m hpi f (T x) := by
    change (Lp.compMeasurePreserving T hT (pullbackLp pi nu m hpi f) : X → ℝ) x = _
    exact hr
  calc
    (pullbackLp pi nu m hpi (koopmanL2 S m hS f) : X → ℝ) x =
        (koopmanL2 S m hS f : Y → ℝ) (pi x) := hl
    _ = f (S (pi x)) := hs'
    _ = f (pi (T x)) := congrArg f (hcomm x).symm
    _ = pullbackLp pi nu m hpi f (T x) := hfx.symm
    _ = (koopmanL2 T nu hT (pullbackLp pi nu m hpi f) : X → ℝ) x := hr'.symm

theorem pullbackLp_birkhoffAverage_koopman
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (pi : X → Y) (nu : Measure X) (m : Measure Y)
    (hpi : MeasurePreserving pi nu m)
    (T : X → X) (S : Y → Y)
    (hT : MeasurePreserving T nu nu) (hS : MeasurePreserving S m m)
    (hcomm : ∀ x, pi (T x) = S (pi x))
    (f : Lp ℝ (2 : ℝ≥0∞) m) (n : ℕ) :
    pullbackLp pi nu m hpi
        (birkhoffAverage ℝ (koopmanL2 S m hS) id n f) =
      birkhoffAverage ℝ (koopmanL2 T nu hT) id n
        (pullbackLp pi nu m hpi f) := by
  rw [map_birkhoffAverage ℝ ℝ (pullbackLp pi nu m hpi)
    (koopmanL2 S m hS) id n f]
  unfold birkhoffAverage birkhoffSum
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hiter : ∀ j : ℕ,
      pullbackLp pi nu m hpi (((koopmanL2 S m hS)^[j]) f) =
        ((koopmanL2 T nu hT)^[j]) (pullbackLp pi nu m hpi f) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          pullbackLp_koopman pi nu m hpi T S hT hS hcomm, ih]
  exact hiter i

theorem lpTensorReal_pullbackLp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (pi : X → Y) (nu : Measure X) (m : Measure Y)
    [IsProbabilityMeasure nu] [IsProbabilityMeasure m]
    (hpi : MeasurePreserving pi nu m)
    (f g : Lp ℝ (2 : ℝ≥0∞) m) :
    lpTensorReal nu (pullbackLp pi nu m hpi f) (pullbackLp pi nu m hpi g) =
      pullbackLp (Prod.map pi pi) (nu.prod nu) (m.prod m) (hpi.prod hpi)
        (lpTensorReal m f g) := by
  apply Lp.ext
  have hf1 := (measurePreserving_fst (μ := nu) (ν := nu)).quasiMeasurePreserving.ae
    (pullbackLp_coe_ae pi nu m hpi f)
  have hg2 := (measurePreserving_snd (μ := nu) (ν := nu)).quasiMeasurePreserving.ae
    (pullbackLp_coe_ae pi nu m hpi g)
  filter_upwards [lpTensorReal_coe_ae nu
      (pullbackLp pi nu m hpi f) (pullbackLp pi nu m hpi g),
    pullbackLp_coe_ae (Prod.map pi pi) (nu.prod nu) (m.prod m)
      (hpi.prod hpi) (lpTensorReal m f g),
    (hpi.prod hpi).quasiMeasurePreserving.ae (lpTensorReal_coe_ae m f g),
    hf1, hg2] with p ht hp hbase hf hg
  rw [ht, hp, hbase, hf, hg]
  rfl

theorem tendsto_pullbackLp_haarDiagonal_lpTensorReal
    {Z X : Type*} [MeasurableSpace Z] [PseudoMetricSpace Z] [T2Space Z]
    [BorelSpace Z] [SecondCountableTopology Z] [CompactSpace Z] [R1Space Z]
    [AddCommGroup Z] [ContinuousAdd Z] [ContinuousSub Z] [ContinuousVAdd Z Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [MeasurableConstVAdd Z Z] [OpensMeasurableSpace Z]
    (m : Measure Z) [IsProbabilityMeasure m] [IsLocallyFiniteMeasure m]
    [m.InnerRegularCompactLTTop] [VAddInvariantMeasure Z Z m]
    [Measure.IsAddLeftInvariant m] [Measure.IsAddRightInvariant m]
    (a : Z) (hrot : Ergodic (fun z : Z => a + z) m)
    [MeasurableSpace X] (nu : Measure X) [IsProbabilityMeasure nu]
    (e : X → X) (he : MeasurePreserving e nu nu)
    (pi : X → Z) (hpi : MeasurePreserving pi nu m)
    (hcomm : ∀ x, pi (e x) = a + pi x)
    (u v : Lp ℝ (2 : ℝ≥0∞) m) :
    Tendsto (fun n => birkhoffAverage ℝ
      (koopmanL2 (Prod.map e e) (nu.prod nu) (he.prod he)) id n
      (lpTensorReal nu (pullbackLp pi nu m hpi u)
        (pullbackLp pi nu m hpi v))) atTop
      (nhds (pullbackLp (Prod.map pi pi) (nu.prod nu) (m.prod m)
        (hpi.prod hpi) (haarCorrelationLp m u v))) := by
  let R : Z → Z := fun z => a + z
  let D : X × X → X × X := Prod.map e e
  let pi2 : X × X → Z × Z := Prod.map pi pi
  let hR : MeasurePreserving R m m := measurePreserving_add_left m a
  let hD : MeasurePreserving D (nu.prod nu) (nu.prod nu) := he.prod he
  let hpi2 : MeasurePreserving pi2 (nu.prod nu) (m.prod m) := hpi.prod hpi
  have hcomm2 : ∀ p, pi2 (D p) = diagonalTransform R (pi2 p) := by
    intro p
    exact Prod.ext (hcomm p.1) (hcomm p.2)
  have hbase := tendsto_haarDiagonal_lpTensorReal m a hrot u v
  have hcont : Tendsto (pullbackLp pi2 (nu.prod nu) (m.prod m) hpi2)
      (nhds (haarCorrelationLp m u v))
      (nhds (pullbackLp pi2 (nu.prod nu) (m.prod m) hpi2
        (haarCorrelationLp m u v))) :=
    (pullbackLp pi2 (nu.prod nu) (m.prod m) hpi2).continuous.continuousAt
  have hmapped := hcont.comp hbase
  have hseq :
      (pullbackLp pi2 (nu.prod nu) (m.prod m) hpi2 ∘
        fun n => birkhoffAverage ℝ
          (koopmanL2 (diagonalTransform R) (m.prod m)
            (measurePreserving_haarDiagonalRotation m a)) id n
          (lpTensorReal m u v)) =
      fun n => birkhoffAverage ℝ
        (koopmanL2 D (nu.prod nu) hD) id n
        (lpTensorReal nu (pullbackLp pi nu m hpi u)
          (pullbackLp pi nu m hpi v)) := by
    funext n
    rw [Function.comp_apply,
      pullbackLp_birkhoffAverage_koopman pi2 (nu.prod nu) (m.prod m)
        hpi2 D (diagonalTransform R) hD
        (measurePreserving_haarDiagonalRotation m a) hcomm2]
    rw [lpTensorReal_pullbackLp pi nu m hpi]
  rw [hseq] at hmapped
  simpa only [R, D, pi2, hD, hpi2] using hmapped

theorem measurePreserving_snd_kroneckerGraphBind
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu) :
    MeasurePreserving Prod.snd (kroneckerGraphBindMeasure T mu hT)
      (kroneckerFactorMeasure T mu hT) := by
  constructor
  · exact measurable_snd
  · rw [kroneckerGraphBindMeasure, bind_kroneckerGraphFiberKernel]
    exact map_snd_kroneckerGraphMeasure T mu hT

noncomputable def kroneckerGraphKernelExpectationLiftLp
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu)
    [BorelSpace (KroneckerGraphSpace T mu hT)]
    (f : BoundedContinuousFunction (KroneckerGraphSpace T mu hT) ℝ) :
    Lp ℝ (2 : ℝ≥0∞) (kroneckerGraphBindMeasure T mu hT) :=
  pullbackLp Prod.snd (kroneckerGraphBindMeasure T mu hT)
    (kroneckerFactorMeasure T mu hT)
    (measurePreserving_snd_kroneckerGraphBind T mu hT)
    (kernelExpectationLp (kroneckerFactorMeasure T mu hT)
      (kroneckerGraphFiberKernel T mu hT) f)

theorem kroneckerGraphKernelExpectationLiftLp_coe_ae
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu)
    [BorelSpace (KroneckerGraphSpace T mu hT)]
    (f : BoundedContinuousFunction (KroneckerGraphSpace T mu hT) ℝ) :
    (kroneckerGraphKernelExpectationLiftLp T mu hT f :
      KroneckerGraphSpace T mu hT → ℝ) =ᵐ[kroneckerGraphBindMeasure T mu hT]
      fun q => kernelExpectation (kroneckerGraphFiberKernel T mu hT) f q.2 := by
  let hpi := measurePreserving_snd_kroneckerGraphBind T mu hT
  filter_upwards [pullbackLp_coe_ae Prod.snd
      (kroneckerGraphBindMeasure T mu hT) (kroneckerFactorMeasure T mu hT)
      hpi (kernelExpectationLp (kroneckerFactorMeasure T mu hT)
        (kroneckerGraphFiberKernel T mu hT) f),
    hpi.quasiMeasurePreserving.ae
      (kernelExpectationLp_coe_ae (kroneckerFactorMeasure T mu hT)
        (kroneckerGraphFiberKernel T mu hT) f)] with q hq hbase
  rw [kroneckerGraphKernelExpectationLiftLp, hq, hbase]

theorem kroneckerGraph_toLp_eq_expectation_add_residual
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (T : X → X) (mu : Measure X) [IsProbabilityMeasure mu]
    (hT : Ergodic T mu)
    [BorelSpace (KroneckerGraphSpace T mu hT)]
    (f : BoundedContinuousFunction (KroneckerGraphSpace T mu hT) ℝ) :
    BoundedContinuousFunction.toLp 2 (kroneckerGraphBindMeasure T mu hT) ℝ f =
      kroneckerGraphKernelExpectationLiftLp T mu hT f +
        kernelResidualRealLp (kroneckerFactorMeasure T mu hT)
          (kroneckerGraphFiberKernel T mu hT) Prod.snd measurable_snd f := by
  apply Lp.ext
  filter_upwards [f.coeFn_toLp 2 (kroneckerGraphBindMeasure T mu hT) ℝ,
    kroneckerGraphKernelExpectationLiftLp_coe_ae T mu hT f,
    kernelResidualRealLp_coe_ae (kroneckerFactorMeasure T mu hT)
      (kroneckerGraphFiberKernel T mu hT) Prod.snd measurable_snd f,
    Lp.coeFn_add (kroneckerGraphKernelExpectationLiftLp T mu hT f)
      (kernelResidualRealLp (kroneckerFactorMeasure T mu hT)
        (kroneckerGraphFiberKernel T mu hT) Prod.snd measurable_snd f)] with
      q hf hl hr hadd
  rw [hf, hadd]
  change f q =
    (kroneckerGraphKernelExpectationLiftLp T mu hT f :
      KroneckerGraphSpace T mu hT → ℝ) q +
    (kernelResidualRealLp (kroneckerFactorMeasure T mu hT)
      (kroneckerGraphFiberKernel T mu hT) Prod.snd measurable_snd f :
      KroneckerGraphSpace T mu hT → ℝ) q
  rw [hl, hr]
  ring

theorem exists_kroneckerGraph_factorTensor_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [BorelSpace (KroneckerGraphSpace e mu he)]
    [MeasurableAdd₂ (KroneckerSubgroup e mu he.toMeasurePreserving)]
    [MeasurableNeg (KroneckerSubgroup e mu he.toMeasurePreserving)]
    (f g : BoundedContinuousFunction (KroneckerGraphSpace e mu he) ℝ) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞)
        ((kroneckerGraphBindMeasure e mu he).prod
          (kroneckerGraphBindMeasure e mu he)),
      Tendsto (fun n => birkhoffAverage ℝ
        (koopmanL2
          (Prod.map (kroneckerGraphMeasurableEquiv e mu he)
            (kroneckerGraphMeasurableEquiv e mu he))
          ((kroneckerGraphBindMeasure e mu he).prod
            (kroneckerGraphBindMeasure e mu he))
          ((measurePreserving_kroneckerGraphBind e mu he).prod
            (measurePreserving_kroneckerGraphBind e mu he)))
        id n
        (lpTensorReal (kroneckerGraphBindMeasure e mu he)
          (kroneckerGraphKernelExpectationLiftLp e mu he f)
          (kroneckerGraphKernelExpectationLiftLp e mu he g)))
        atTop (nhds L) ∧
      (L : (KroneckerGraphSpace e mu he) ×
          (KroneckerGraphSpace e mu he) → ℝ) =ᵐ[
            (kroneckerGraphBindMeasure e mu he).prod
              (kroneckerGraphBindMeasure e mu he)]
        fun p => componentMoment
          (factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd)
          (separatedBCF f g) p := by
  let : Countable (KoopmanEigenvalueType e mu he.toMeasurePreserving) :=
    (countable_koopmanEigenvalues e mu he.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup e mu he.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let : BorelSpace H := inferInstance
  let : PseudoMetricSpace H :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric H
  let m := kroneckerFactorMeasure e mu he
  let eta := kroneckerGraphFiberKernel e mu he
  let nu := kroneckerGraphBindMeasure e mu he
  let E := kroneckerGraphMeasurableEquiv e mu he
  let alpha := kroneckerSubgroupRotation e mu he
  let : Measure.IsAddHaarMeasure m :=
    isAddHaarMeasure_kroneckerFactorMeasure e mu he
  let hpi := measurePreserving_snd_kroneckerGraphBind e mu he
  let hE := measurePreserving_kroneckerGraphBind e mu he
  let u := kernelExpectationLp m eta f
  let v := kernelExpectationLp m eta g
  let pi2 : (KroneckerGraphSpace e mu he) × (KroneckerGraphSpace e mu he) →
      H × H := Prod.map Prod.snd Prod.snd
  let hpi2 : MeasurePreserving pi2 (nu.prod nu) (m.prod m) := hpi.prod hpi
  let L : Lp ℝ (2 : ℝ≥0∞) (nu.prod nu) :=
    pullbackLp pi2 (nu.prod nu) (m.prod m) hpi2
      (haarCorrelationLp m u v)
  refine ⟨L, ?_, ?_⟩
  · have hfactor := tendsto_pullbackLp_haarDiagonal_lpTensorReal
      m alpha (ergodic_kroneckerSubgroupRotation e mu he)
      nu E hE Prod.snd hpi (fun q => rfl) u v
    simpa only [m, eta, nu, E, alpha, u, v, pi2, hpi2, L,
      kroneckerGraphKernelExpectationLiftLp] using hfactor
  · have hL := pullbackLp_coe_ae pi2 (nu.prod nu) (m.prod m) hpi2
      (haarCorrelationLp m u v)
    have hcorr := hpi2.quasiMeasurePreserving.ae
      (haarCorrelationLp_coe_ae m u v)
    filter_upwards [hL, hcorr] with p hp hcp
    rw [hp, hcp]
    exact (componentMoment_factorComponent_separated_eq_inner
      m eta Prod.snd f g p).symm

theorem birkhoffAverage_continuousLinearMap_add
    {R V : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup V] [NormedSpace R V]
    (U : V →L[R] V) (n : ℕ) (x y : V) :
    birkhoffAverage R U id n (x + y) =
      birkhoffAverage R U id n x + birkhoffAverage R U id n y := by
  unfold birkhoffAverage birkhoffSum
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [id_eq]
  have hiterate : ∀ j : ℕ,
      (U : V → V)^[j] (x + y) =
        (U : V → V)^[j] x + (U : V → V)^[j] y := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', ih, map_add]
  exact hiterate i

theorem birkhoffAverage_continuousLinearMap_smul
    {R V : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup V] [NormedSpace R V]
    (U : V →L[R] V) (n : ℕ) (r : R) (x : V) :
    birkhoffAverage R U id n (r • x) =
      r • birkhoffAverage R U id n x := by
  unfold birkhoffAverage birkhoffSum
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [id_eq]
  have hiterate : ∀ j : ℕ,
      (U : V → V)^[j] (r • x) = r • (U : V → V)^[j] x := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_smul]
  exact hiterate i

theorem exists_kroneckerGraph_separated_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [BorelSpace (KroneckerGraphSpace e mu he)]
    [SecondCountableTopology (KroneckerGraphSpace e mu he)]
    [MeasurableAdd₂ (KroneckerSubgroup e mu he.toMeasurePreserving)]
    [MeasurableNeg (KroneckerSubgroup e mu he.toMeasurePreserving)]
    (f g : BoundedContinuousFunction (KroneckerGraphSpace e mu he) ℝ) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞)
        ((kroneckerGraphBindMeasure e mu he).prod
          (kroneckerGraphBindMeasure e mu he)),
      Tendsto (fun n => birkhoffAverage ℝ
        (koopmanL2
          (Prod.map (kroneckerGraphMeasurableEquiv e mu he)
            (kroneckerGraphMeasurableEquiv e mu he))
          ((kroneckerGraphBindMeasure e mu he).prod
            (kroneckerGraphBindMeasure e mu he))
          ((measurePreserving_kroneckerGraphBind e mu he).prod
            (measurePreserving_kroneckerGraphBind e mu he)))
        id (n + 1)
        (BoundedContinuousFunction.toLp 2
          ((kroneckerGraphBindMeasure e mu he).prod
            (kroneckerGraphBindMeasure e mu he)) ℝ (separatedBCF f g)))
        atTop (nhds L) ∧
      (L : (KroneckerGraphSpace e mu he) ×
          (KroneckerGraphSpace e mu he) → ℝ) =ᵐ[
            (kroneckerGraphBindMeasure e mu he).prod
              (kroneckerGraphBindMeasure e mu he)]
        fun p => componentMoment
          (factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd)
          (separatedBCF f g) p := by
  let nu := kroneckerGraphBindMeasure e mu he
  let E := kroneckerGraphMeasurableEquiv e mu he
  let hE := measurePreserving_kroneckerGraphBind e mu he
  let U := koopmanL2 (Prod.map E E) (nu.prod nu) (hE.prod hE)
  let lf := kroneckerGraphKernelExpectationLiftLp e mu he f
  let lg := kroneckerGraphKernelExpectationLiftLp e mu he g
  let rf := kernelResidualRealLp (kroneckerFactorMeasure e mu he)
    (kroneckerGraphFiberKernel e mu he) Prod.snd measurable_snd f
  let rg := kernelResidualRealLp (kroneckerFactorMeasure e mu he)
    (kroneckerGraphFiberKernel e mu he) Prod.snd measurable_snd g
  let wf := BoundedContinuousFunction.toLp 2 nu ℝ f
  let wg := BoundedContinuousFunction.toLp 2 nu ℝ g
  obtain ⟨L, hfactor, hL⟩ := exists_kroneckerGraph_factorTensor_limit e mu he f g
  refine ⟨L, ?_, hL⟩
  have hfactor' : Tendsto (fun n => birkhoffAverage ℝ U id (n + 1)
      (lpTensorReal nu lf lg)) atTop (nhds L) := by
    simpa only [nu, E, hE, U, lf, lg, Function.comp_def] using
      hfactor.comp (tendsto_add_atTop_nat 1)
  have hleft : Tendsto (fun n => birkhoffAverage ℝ U id (n + 1)
      (lpTensorReal nu rf wg)) atTop (nhds 0) := by
    simpa only [nu, E, hE, U, rf, wg] using
      tendsto_kroneckerGraphResidual_lpTensorReal_average_zero
        e mu he f (BoundedContinuousFunction.toLp 2 nu ℝ g)
  have hright : Tendsto (fun n => birkhoffAverage ℝ U id (n + 1)
      (lpTensorReal nu lf rg)) atTop (nhds 0) := by
    simpa only [nu, E, hE, U, lf, rg] using
      tendsto_kroneckerGraphResidual_lpTensorReal_average_zero_right
        e mu he (kroneckerGraphKernelExpectationLiftLp e mu he f) g
  have hdf : wf = lf + rf := by
    simpa only [nu, wf, lf, rf] using
      kroneckerGraph_toLp_eq_expectation_add_residual e mu he f
  have hdg : wg = lg + rg := by
    simpa only [nu, wg, lg, rg] using
      kroneckerGraph_toLp_eq_expectation_add_residual e mu he g
  have hfirst : lpTensorReal nu wf wg =
      lpTensorReal nu lf wg + lpTensorReal nu rf wg := by
    rw [hdf, lpTensorReal_add_left]
  have hsecond : lpTensorReal nu lf wg =
      lpTensorReal nu lf lg + lpTensorReal nu lf rg := by
    rw [hdg, lpTensorReal_add_right]
  have htensor : lpTensorReal nu wf wg =
      (lpTensorReal nu lf lg + lpTensorReal nu lf rg) +
        lpTensorReal nu rf wg := by
    rw [hfirst, hsecond]
  have hsum : Tendsto (fun n =>
      (birkhoffAverage ℝ U id (n + 1) (lpTensorReal nu lf lg) +
        birkhoffAverage ℝ U id (n + 1) (lpTensorReal nu lf rg)) +
      birkhoffAverage ℝ U id (n + 1) (lpTensorReal nu rf wg))
      atTop (nhds L) := by
    simpa using (hfactor'.add hright).add hleft
  have hsep : BoundedContinuousFunction.toLp 2 (nu.prod nu) ℝ
      (separatedBCF f g) = lpTensorReal nu wf wg := by
    exact (lpTensorReal_toLp_separated nu f g).symm
  simpa only [nu, E, hE, U, wf, wg, hsep, htensor,
    birkhoffAverage_continuousLinearMap_add] using hsum

theorem exists_kroneckerGraph_subalgebra_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [BorelSpace (KroneckerGraphSpace e mu he)]
    [SecondCountableTopology (KroneckerGraphSpace e mu he)]
    [CompactSpace (KroneckerGraphSpace e mu he)]
    [MeasurableAdd₂ (KroneckerSubgroup e mu he.toMeasurePreserving)]
    [MeasurableNeg (KroneckerSubgroup e mu he.toMeasurePreserving)]
    (F : C((KroneckerGraphSpace e mu he) ×
      (KroneckerGraphSpace e mu he), ℝ))
    (hF : F ∈ separatedContinuousSubalgebra (KroneckerGraphSpace e mu he)) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞)
        ((kroneckerGraphBindMeasure e mu he).prod
          (kroneckerGraphBindMeasure e mu he)),
      Tendsto (fun n => birkhoffAverage ℝ
        (koopmanL2
          (Prod.map (kroneckerGraphMeasurableEquiv e mu he)
            (kroneckerGraphMeasurableEquiv e mu he))
          ((kroneckerGraphBindMeasure e mu he).prod
            (kroneckerGraphBindMeasure e mu he))
          ((measurePreserving_kroneckerGraphBind e mu he).prod
            (measurePreserving_kroneckerGraphBind e mu he)))
        id (n + 1)
        (BoundedContinuousFunction.toLp 2
          ((kroneckerGraphBindMeasure e mu he).prod
            (kroneckerGraphBindMeasure e mu he)) ℝ
          (BoundedContinuousFunction.mkOfCompact F)))
        atTop (nhds L) ∧
      (L : (KroneckerGraphSpace e mu he) ×
          (KroneckerGraphSpace e mu he) → ℝ) =ᵐ[
            (kroneckerGraphBindMeasure e mu he).prod
              (kroneckerGraphBindMeasure e mu he)]
        fun p => componentMoment
          (factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd)
          (BoundedContinuousFunction.mkOfCompact F) p := by
  let Q := KroneckerGraphSpace e mu he
  let nu := kroneckerGraphBindMeasure e mu he
  let E := kroneckerGraphMeasurableEquiv e mu he
  let hE := measurePreserving_kroneckerGraphBind e mu he
  let U := koopmanL2 (Prod.map E E) (nu.prod nu) (hE.prod hE)
  change F ∈ Submodule.span ℝ
    (Set.range (fun fg : C(Q, ℝ) × C(Q, ℝ) =>
      separatedContinuousMap fg.1 fg.2)) at hF
  refine Submodule.span_induction
    (p := fun F _ => ∃ L : Lp ℝ (2 : ℝ≥0∞) (nu.prod nu),
      Tendsto (fun n => birkhoffAverage ℝ U id (n + 1)
        (BoundedContinuousFunction.toLp 2 (nu.prod nu) ℝ
          (BoundedContinuousFunction.mkOfCompact F))) atTop (nhds L) ∧
      (L : Q × Q → ℝ) =ᵐ[nu.prod nu] fun p => componentMoment
        (factorComponent (kroneckerFactorMeasure e mu he)
          (kroneckerGraphFiberKernel e mu he) Prod.snd)
        (BoundedContinuousFunction.mkOfCompact F) p)
    ?_ ?_ ?_ ?_ hF
  · intro G hG
    rcases hG with ⟨fg, rfl⟩
    let f := BoundedContinuousFunction.mkOfCompact fg.1
    let g := BoundedContinuousFunction.mkOfCompact fg.2
    have hsep : BoundedContinuousFunction.mkOfCompact
        (separatedContinuousMap fg.1 fg.2) = separatedBCF f g := by
      ext p
      rfl
    simpa only [Q, nu, E, hE, U, hsep] using
      exists_kroneckerGraph_separated_limit e mu he f g
  · refine ⟨0, ?_, ?_⟩
    · simp [BoundedContinuousFunction.toLp, birkhoffAverage, birkhoffSum]
    · filter_upwards [Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (nu.prod nu)] with p hp
      simp [componentMoment]
  · intro F G hFs hGs hFlim hGlim
    obtain ⟨LF, hFt, hFae⟩ := hFlim
    obtain ⟨LG, hGt, hGae⟩ := hGlim
    refine ⟨LF + LG, ?_, ?_⟩
    · have hadd := hFt.add hGt
      simpa only [BoundedContinuousFunction.mkOfCompact_add, map_add,
        birkhoffAverage_continuousLinearMap_add] using hadd
    · filter_upwards [Lp.coeFn_add LF LG, hFae, hGae] with p hadd hFp hGp
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hFp, hGp]
      unfold componentMoment
      rw [BoundedContinuousFunction.mkOfCompact_add]
      change (∫ q, (BoundedContinuousFunction.mkOfCompact F) q
          ∂(factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd p : Measure (Q × Q))) +
        ∫ q, (BoundedContinuousFunction.mkOfCompact G) q
          ∂(factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd p : Measure (Q × Q)) =
        ∫ q, (BoundedContinuousFunction.mkOfCompact F) q +
            (BoundedContinuousFunction.mkOfCompact G) q
          ∂(factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd p : Measure (Q × Q))
      rw [integral_add
        ((BoundedContinuousFunction.mkOfCompact F).integrable _)
        ((BoundedContinuousFunction.mkOfCompact G).integrable _)]
  · intro r F hFs hFlim
    obtain ⟨L, ht, hL⟩ := hFlim
    have hbcf : BoundedContinuousFunction.mkOfCompact (r • F) =
        r • BoundedContinuousFunction.mkOfCompact F := by
      ext p
      rfl
    refine ⟨r • L, ?_, ?_⟩
    · have hsmul := ht.const_smul r
      simpa only [hbcf, map_smul,
        birkhoffAverage_continuousLinearMap_smul] using hsmul
    · filter_upwards [Lp.coeFn_smul r L, hL] with p hsmul hp
      rw [hsmul]
      simp only [Pi.smul_apply]
      rw [hp, hbcf]
      unfold componentMoment
      change r * (∫ q, (BoundedContinuousFunction.mkOfCompact F) q
          ∂(factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd p : Measure (Q × Q))) =
        ∫ q, r * (BoundedContinuousFunction.mkOfCompact F) q
          ∂(factorComponent (kroneckerFactorMeasure e mu he)
            (kroneckerGraphFiberKernel e mu he) Prod.snd p : Measure (Q × Q))
      rw [integral_const_mul]

theorem exists_dense_kroneckerGraph_subalgebra_seq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [T2Space (KroneckerGraphSpace e mu he)]
    [SecondCountableTopology (KroneckerGraphSpace e mu he)]
    [CompactSpace (KroneckerGraphSpace e mu he)] :
    ∃ G : ℕ → BoundedContinuousFunction
        ((KroneckerGraphSpace e mu he) × (KroneckerGraphSpace e mu he)) ℝ,
      DenseRange G ∧
      ∀ j, (G j).toContinuousMap ∈
        separatedContinuousSubalgebra (KroneckerGraphSpace e mu he) := by
  let Q := KroneckerGraphSpace e mu he
  let : SecondCountableTopology Q := inferInstance
  let : CompactSpace Q := inferInstance
  let : T2Space Q := inferInstance
  let : PseudoMetricSpace Q :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric Q
  let : MetricSpace Q := MetricSpace.ofT0PseudoMetricSpace Q
  let D : ℕ → C(Q × Q, ℝ) := TopologicalSpace.denseSeq C(Q × Q, ℝ)
  have hD : DenseRange D := by
    simpa only [D] using
      (TopologicalSpace.denseRange_denseSeq C(Q × Q, ℝ))
  let A := separatedContinuousSubalgebra Q
  have hAsep : A.SeparatesPoints := by
    simpa only [A, Q] using
      (separatedContinuousSubalgebra_separatesPoints
        (KroneckerGraphSpace e mu he))
  let approx : ℕ → ℕ → A := fun j k => Classical.choose
    (ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      A hAsep (D j)
        (1 / ((k : ℝ) + 1)) (by positivity))
  have happrox (j k : ℕ) :
      ‖(approx j k : C(Q × Q, ℝ)) - D j‖ < 1 / ((k : ℝ) + 1) :=
    Classical.choose_spec
      (ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
        A hAsep (D j)
          (1 / ((k : ℝ) + 1)) (by positivity))
  let G : ℕ → BoundedContinuousFunction (Q × Q) ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (approx n.unpair.1 n.unpair.2 : C(Q × Q, ℝ))
  refine ⟨G, ?_, ?_⟩
  · change Dense (Set.range G)
    rw [Metric.dense_iff]
    intro f eps heps
    obtain ⟨j, hj⟩ := hD.exists_dist_lt f.toContinuousMap
      (show 0 < eps / 2 by positivity)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < eps / 2 by positivity)
    refine ⟨G (Nat.pair j k), ?_, ⟨Nat.pair j k, rfl⟩⟩
    rw [Metric.mem_ball]
    have hleft : dist (G (Nat.pair j k))
        (BoundedContinuousFunction.mkOfCompact (D j)) < eps / 2 := by
      calc
        dist (G (Nat.pair j k))
            (BoundedContinuousFunction.mkOfCompact (D j)) =
            ‖(approx j k : C(Q × Q, ℝ)) - D j‖ := by
              simp only [G, Nat.unpair_pair, dist_eq_norm]
              rw [← BoundedContinuousFunction.mkOfCompact_sub,
                BoundedContinuousFunction.norm_mkOfCompact]
        _ < 1 / ((k : ℝ) + 1) := happrox j k
        _ < eps / 2 := hk
    have hright : dist (BoundedContinuousFunction.mkOfCompact (D j)) f < eps / 2 := by
      change dist (D j) f.toContinuousMap < eps / 2
      simpa only [dist_comm] using hj
    calc
      dist (G (Nat.pair j k)) f ≤
          dist (G (Nat.pair j k)) (BoundedContinuousFunction.mkOfCompact (D j)) +
            dist (BoundedContinuousFunction.mkOfCompact (D j)) f := dist_triangle _ _ _
      _ < eps / 2 + eps / 2 := add_lt_add hleft hright
      _ = eps := by ring
  · intro j
    change (approx j.unpair.1 j.unpair.2 : C(Q × Q, ℝ)) ∈ A
    exact (approx j.unpair.1 j.unpair.2).property

theorem exists_kroneckerGraph_generic_component
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [PseudoMetricSpace (KroneckerGraphSpace e mu he)]
    [T2Space (KroneckerGraphSpace e mu he)]
    [BorelSpace (KroneckerGraphSpace e mu he)]
    [SecondCountableTopology (KroneckerGraphSpace e mu he)]
    [CompactSpace (KroneckerGraphSpace e mu he)]
    [MeasurableAdd₂ (KroneckerSubgroup e mu he.toMeasurePreserving)]
    [MeasurableNeg (KroneckerSubgroup e mu he.toMeasurePreserving)] :
    ∃ b : KroneckerGraphSpace e mu he,
      b ∈ (kroneckerGraphBindMeasure e mu he).support ∧
      ∃ baseLength : ℕ → ℕ, Tendsto baseLength atTop atTop ∧
        ∀ᵐ x ∂kroneckerGraphBindMeasure e mu he,
          ∀ f : BoundedContinuousFunction
              ((KroneckerGraphSpace e mu he) × (KroneckerGraphSpace e mu he)) ℝ,
            Tendsto
              (fun n => birkhoffAverage ℝ
                (diagonalTransform (kroneckerGraphMeasurableEquiv e mu he)) f
                (baseLength n) (b, x))
              atTop
              (nhds (componentMoment
                (factorComponent (kroneckerFactorMeasure e mu he)
                  (kroneckerGraphFiberKernel e mu he) Prod.snd) f (b, x))) := by
  let Q := KroneckerGraphSpace e mu he
  let nu := kroneckerGraphBindMeasure e mu he
  let E := kroneckerGraphMeasurableEquiv e mu he
  let hE := measurePreserving_kroneckerGraphBind e mu he
  let component := factorComponent (kroneckerFactorMeasure e mu he)
    (kroneckerGraphFiberKernel e mu he) Prod.snd
  obtain ⟨G, hGdense, hGmem⟩ :=
    exists_dense_kroneckerGraph_subalgebra_seq e mu he
  let actual : ℕ → ℕ → Q × Q → ℝ := fun j n p =>
    birkhoffAverage ℝ (Prod.map E E) (G j) (n + 1) p
  let target : ℕ → Q × Q → ℝ := fun j p =>
    componentMoment component (G j) p
  have hmeasure (j : ℕ) :
      TendstoInMeasure (nu.prod nu) (actual j) atTop (target j) := by
    obtain ⟨L, hlim, hLae⟩ := exists_kroneckerGraph_subalgebra_limit
      e mu he (G j).toContinuousMap (hGmem j)
    have hGj : BoundedContinuousFunction.mkOfCompact (G j).toContinuousMap = G j := by
      ext p
      rfl
    rw [hGj] at hlim hLae
    have hm := tendstoInMeasure_of_tendsto_Lp hlim
    have hm' : TendstoInMeasure (nu.prod nu) (actual j) atTop (L : Q × Q → ℝ) := by
      apply TendstoInMeasure.congr_left (fun n => ?_) hm
      simpa only [Q, nu, E, hE, actual] using
        (coe_birkhoffAverage_toLp_ae
          (Prod.map E E) (nu.prod nu) (hE.prod hE) (G j) (n + 1))
    exact TendstoInMeasure.congr_right (by
      simpa only [Q, nu, component, target] using hLae) hm'
  obtain ⟨ns, hns, hpoint⟩ := exists_diagonal_tendsto_ae actual target hmeasure
  have hsections : ∀ᵐ b ∂nu, ∀ᵐ x ∂nu, ∀ j,
      Tendsto (fun n => actual j (ns n) (b, x)) atTop (nhds (target j (b, x))) :=
    Measure.ae_ae_of_ae_prod hpoint
  obtain ⟨b, hbtypical, hbsupport⟩ :=
    (hsections.and Measure.support_mem_ae).exists
  let baseLength : ℕ → ℕ := fun n => ns n + 1
  refine ⟨b, hbsupport, baseLength, (tendsto_add_atTop_nat 1).comp hns, ?_⟩
  have hdiag : Prod.map (E : Q → Q) E = diagonalTransform E := by
    funext p
    rfl
  rw [← hdiag]
  filter_upwards [hbtypical] with x hx
  intro f
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨j, hj⟩ := hGdense.exists_dist_lt f (show 0 < eps / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hx j) (eps / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have havg : dist
      (birkhoffAverage ℝ (Prod.map E E) f (baseLength n) (b, x))
      (birkhoffAverage ℝ (Prod.map E E) (G j) (baseLength n) (b, x)) ≤
        ‖f - G j‖ := by
    simpa only [Real.dist_eq] using
      abs_birkhoffAverage_sub_le_norm (Prod.map E E) f (G j)
        (baseLength n) (b, x)
  have hint : dist (componentMoment component (G j) (b, x))
      (componentMoment component f (b, x)) ≤ ‖f - G j‖ := by
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_integral_sub_le_norm (component (b, x) : Measure (Q × Q)) f (G j)
  have hnorm : ‖f - G j‖ < eps / 3 := by
    simpa only [dist_eq_norm] using hj
  have hmiddle : dist
      (birkhoffAverage ℝ (Prod.map E E) (G j) (baseLength n) (b, x))
      (componentMoment component (G j) (b, x)) < eps / 3 := by
    simpa only [actual, target, baseLength] using hN n hn
  calc
    dist (birkhoffAverage ℝ (Prod.map E E) f (baseLength n) (b, x))
        (componentMoment component f (b, x)) ≤
      dist (birkhoffAverage ℝ (Prod.map E E) f (baseLength n) (b, x))
          (birkhoffAverage ℝ (Prod.map E E) (G j) (baseLength n) (b, x)) +
        dist (birkhoffAverage ℝ (Prod.map E E) (G j) (baseLength n) (b, x))
          (componentMoment component (G j) (b, x)) +
        dist (componentMoment component (G j) (b, x))
          (componentMoment component f (b, x)) := dist_triangle4 _ _ _ _
    _ < eps / 3 + eps / 3 + eps / 3 :=
      add_lt_add (add_lt_add (havg.trans_lt hnorm) hmiddle) (hint.trans_lt hnorm)
    _ = eps := by ring

end Erdos656
namespace Erdos656

open Filter Function Set Topology MeasureTheory
open ProbabilityTheory
open scoped ENNReal Pointwise Topology symmDiff

noncomputable def rightTranslationContinuousMap
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z]
    (q : Z) : C(Z, Z) :=
  ⟨fun z ↦ z + q, continuous_id.add continuous_const⟩

theorem continuous_rightTranslationContinuousMap
    {Z : Type*} [TopologicalSpace Z] [Add Z] [ContinuousAdd Z] :
    Continuous (rightTranslationContinuousMap : Z → C(Z, Z)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  convert ((continuous_snd : Continuous (fun p : Z × Z ↦ p.2)).add continuous_fst) using 1
  funext p
  rfl

theorem tendsto_measure_rightTranslation_symmDiff
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    {S : Set Z} (hS : MeasurableSet S) :
    Tendsto (fun q : Z ↦ m (((fun z : Z ↦ z + q) ⁻¹' S) ∆ S))
      (𝓝 0) (𝓝 0) := by
  have h := MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero
    ((continuous_rightTranslationContinuousMap (Z := Z)).tendsto 0)
    (Eventually.of_forall fun q ↦ measurePreserving_add_right m q)
    (measurePreserving_add_right m 0) hS.nullMeasurableSet (measure_ne_top m S)
  change Tendsto (fun q : Z ↦
    m (((fun z : Z ↦ z + q) ⁻¹' S) ∆ ((fun z : Z ↦ z + 0) ⁻¹' S)))
      (𝓝 0) (𝓝 0) at h
  simpa only [add_zero, preimage_id'] using h

theorem exists_open_translationControl
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) :
    ∃ Q : Set Z, IsOpen Q ∧ 0 ∈ Q ∧
      ∀ i ≤ n, ∀ q ∈ Q,
        m (((fun z : Z ↦ z + q) ⁻¹' S i) ∆ S i) <
          (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
  have hall : ∀ᶠ q : Z in 𝓝 0, ∀ i ∈ Finset.range (n + 1),
      m (((fun z : Z ↦ z + q) ⁻¹' S i) ∆ S i) <
        (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
    rw [Finset.eventually_all]
    intro i hi
    exact (tendsto_order.1 (tendsto_measure_rightTranslation_symmDiff m (hS i))).2
      _ (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _)
  obtain ⟨Q, hQsub, hQopen, hQzero⟩ := mem_nhds_iff.mp hall
  refine ⟨Q, hQopen, hQzero, ?_⟩
  intro i hi q hq
  exact hQsub hq i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))

def haarFailureSet
    {Z : Type*} [Add Z] (S Q : Set Z) : Set (Z × Z) :=
  {p | p.1 ∈ S ∧ p.2 ∈ Q ∧ p.1 + p.2 ∉ S}

theorem measurableSet_haarFailureSet
    {Z : Type*} [MeasurableSpace Z] [Add Z] [MeasurableAdd₂ Z]
    {S Q : Set Z} (hS : MeasurableSet S) (hQ : MeasurableSet Q) :
    MeasurableSet (haarFailureSet S Q) := by
  exact (hS.preimage measurable_fst).inter
    ((hQ.preimage measurable_snd).inter
      (hS.preimage (measurable_fst.add measurable_snd)).compl)

theorem measure_goodSection_eq_numerator
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [Measure.IsAddLeftInvariant m]
    (S Q : Set Z) (z : Z) :
    m {q : Z | q ∈ Q ∧ z + q ∈ S} =
      m (S ∩ leftAddTranslate z Q) := by
  have h := measure_preimage_add_right m z (S ∩ leftAddTranslate z Q)
  rw [← h]
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
    leftAddTranslate]
  constructor
  · rintro ⟨hqQ, hzqS⟩
    constructor
    · simpa only [add_comm] using hzqS
    · simpa only [add_sub_cancel_right] using hqQ
  · rintro ⟨hqS, hqQ⟩
    constructor
    · simpa only [add_sub_cancel_right] using hqQ
    · simpa only [add_comm] using hqS

theorem measure_haarFailureSet_le
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [SFinite m] [Measure.IsAddLeftInvariant m]
    {S Q : Set Z} (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    {eps : ℝ≥0∞}
    (hcontrol : ∀ q ∈ Q,
      m (((fun z : Z ↦ z + q) ⁻¹' S) ∆ S) ≤ eps) :
    (m.prod m) (haarFailureSet S Q) ≤ eps * m Q := by
  rw [Measure.prod_apply_symm (measurableSet_haarFailureSet hS hQ)]
  calc
    (∫⁻ q, m ((fun z : Z ↦ (z, q)) ⁻¹' haarFailureSet S Q) ∂m) ≤
        ∫⁻ q in Q, eps ∂m := by
      rw [← lintegral_indicator hQ]
      apply lintegral_mono
      intro q
      by_cases hq : q ∈ Q
      · simp only [hq, Set.indicator_of_mem]
        apply (measure_mono ?_).trans (hcontrol q hq)
        intro z hz
        exact Or.inr ⟨hz.1, hz.2.2⟩
      · change m ((fun z : Z ↦ (z, q)) ⁻¹' haarFailureSet S Q) ≤
          Q.indicator (fun _ ↦ eps) q
        simp [haarFailureSet, hq]
    _ = eps * m Q := setLIntegral_const Q eps

def haarFailureMass
    {Z : Type*} [MeasurableSpace Z] [Add Z]
    (m : Measure Z) (S Q : Set Z) (z : Z) : ℝ≥0∞ :=
  m {q : Z | z ∈ S ∧ q ∈ Q ∧ z + q ∉ S}

def haarBadSet
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    (m : Measure Z) (S Q : Set Z) : Set Z :=
  {z | z ∈ S ∧
    (4 : ℝ≥0∞) * m (S ∩ leftAddTranslate z Q) ≤ (3 : ℝ≥0∞) * m Q}

theorem measurable_haarFailureMass
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [SFinite m]
    {S Q : Set Z} (hS : MeasurableSet S) (hQ : MeasurableSet Q) :
    Measurable (haarFailureMass m S Q) := by
  have hF := measurableSet_haarFailureSet hS hQ
  convert (measurable_measure_prodMk_left (ν := m) hF) using 1
  funext z
  apply congrArg m
  ext q
  rfl

theorem measurableSet_haarBadSet
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [SFinite m]
    {S Q : Set Z} (hS : MeasurableSet S) (hQ : MeasurableSet Q) :
    MeasurableSet (haarBadSet m S Q) := by
  have hnum : Measurable (fun z : Z ↦
      m (S ∩ leftAddTranslate z Q)) := by
    let R : Set (Z × Z) := {p | p.2 ∈ S ∧ p.2 - p.1 ∈ Q}
    have hR : MeasurableSet R :=
      (hS.preimage measurable_snd).inter
        (hQ.preimage (measurable_snd.sub measurable_fst))
    convert (measurable_measure_prodMk_left (ν := m) hR) using 1
    funext z
    congr 1
  exact hS.inter (measurableSet_le (measurable_const.mul hnum)
    (measurable_const.mul measurable_const))

theorem quarter_measure_le_haarFailureMass_of_mem_bad
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [IsFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    {S Q : Set Z} (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    {z : Z} (hz : z ∈ haarBadSet m S Q) :
    (1 / 4 : ℝ≥0∞) * m Q ≤ haarFailureMass m S Q z := by
  let G : Set Z := {q : Z | q ∈ Q ∧ z + q ∈ S}
  let F : Set Z := {q : Z | q ∈ Q ∧ z + q ∉ S}
  have hG : MeasurableSet G := hQ.inter
    (hS.preimage (measurable_const.add measurable_id))
  have hF : MeasurableSet F := hQ.inter
    (hS.preimage (measurable_const.add measurable_id)).compl
  have hdisj : Disjoint G F := by
    refine Set.disjoint_left.2 ?_
    intro q hqG hqF
    exact hqF.2 hqG.2
  have hunion : G ∪ F = Q := by
    ext q
    simp only [G, F, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hsum : m G + m F = m Q := by
    rw [← hunion, measure_union hdisj hF]
  have hgood : m G = m (S ∩ leftAddTranslate z Q) :=
    measure_goodSection_eq_numerator m S Q z
  have hbad : (4 : ℝ≥0∞) * m G ≤ (3 : ℝ≥0∞) * m Q := by
    simpa only [haarBadSet, Set.mem_ofPred_eq, hgood] using hz.2
  have hfiniteG : m G ≠ ∞ := measure_ne_top m G
  have hfiniteF : m F ≠ ∞ := measure_ne_top m F
  have hfiniteQ : m Q ≠ ∞ := measure_ne_top m Q
  have hsumR : (m G).toReal + (m F).toReal = (m Q).toReal := by
    simpa only [ENNReal.toReal_add hfiniteG hfiniteF] using congrArg ENNReal.toReal hsum
  have hbadR : 4 * (m G).toReal ≤ 3 * (m Q).toReal := by
    have := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (by norm_num) hfiniteG)
      (ENNReal.mul_ne_top (by norm_num) hfiniteQ)).mpr hbad
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using this
  have hmass : haarFailureMass m S Q z = m F := by
    unfold haarFailureMass
    apply congrArg m
    ext q
    simp only [F, Set.mem_ofPred_eq, hz.1, true_and]
  rw [hmass]
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (by norm_num) hfiniteQ) hfiniteF).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat]
  change (1 / 4 : ℝ) * (m Q).toReal ≤ (m F).toReal
  linarith

theorem measure_haarBadSet_le
    {Z : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    (m : Measure Z) [IsFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    {S Q : Set Z} (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (hQpos : 0 < m Q) {eps : ℝ≥0∞} (heps : eps ≠ ∞)
    (hcontrol : ∀ q ∈ Q,
      m (((fun z : Z ↦ z + q) ⁻¹' S) ∆ S) ≤ eps) :
    m (haarBadSet m S Q) ≤ 4 * eps := by
  let a : ℝ≥0∞ := (1 / 4 : ℝ≥0∞) * m Q
  let threshold : Set Z := {z | a ≤ haarFailureMass m S Q z}
  have hbadsub : haarBadSet m S Q ⊆ threshold := by
    intro z hz
    exact quarter_measure_le_haarFailureMass_of_mem_bad m hS hQ hz
  have hmeasFail : Measurable (haarFailureMass m S Q) :=
    measurable_haarFailureMass m hS hQ
  have hmarkov : a * m threshold ≤ ∫⁻ z, haarFailureMass m S Q z ∂m := by
    exact mul_meas_ge_le_lintegral hmeasFail a
  have hintegral : (∫⁻ z, haarFailureMass m S Q z ∂m) =
      (m.prod m) (haarFailureSet S Q) := by
    rw [Measure.prod_apply (measurableSet_haarFailureSet hS hQ)]
    rfl
  have hmain : a * m (haarBadSet m S Q) ≤ eps * m Q := by
    calc
      a * m (haarBadSet m S Q) ≤ a * m threshold :=
        mul_le_mul_right (measure_mono hbadsub) a
      _ ≤ ∫⁻ z, haarFailureMass m S Q z ∂m := hmarkov
      _ = (m.prod m) (haarFailureSet S Q) := hintegral
      _ ≤ eps * m Q := measure_haarFailureSet_le m hS hQ hcontrol
  have hfiniteQ : m Q ≠ ∞ := measure_ne_top m Q
  have hfiniteBad : m (haarBadSet m S Q) ≠ ∞ := measure_ne_top m _
  have hfiniteA : a ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) hfiniteQ
  have hfiniteL : a * m (haarBadSet m S Q) ≠ ∞ :=
    ENNReal.mul_ne_top hfiniteA hfiniteBad
  have hfiniteR : eps * m Q ≠ ∞ := ENNReal.mul_ne_top heps hfiniteQ
  have hmainR := (ENNReal.toReal_le_toReal hfiniteL hfiniteR).mpr hmain
  have hQreal : 0 < (m Q).toReal := ENNReal.toReal_pos hQpos.ne' hfiniteQ
  have hresultR : (m (haarBadSet m S Q)).toReal ≤ 4 * eps.toReal := by
    dsimp only [a] at hmainR
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat] at hmainR
    nlinarith
  exact (ENNReal.toReal_le_toReal hfiniteBad
    (ENNReal.mul_ne_top (by norm_num) heps)).mp (by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hresultR)

noncomputable def commonHaarNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) : Set Z :=
  (exists_open_translationControl m S hS n).choose

theorem isOpen_commonHaarNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) :
    IsOpen (commonHaarNeighborhood m S hS n) :=
  (exists_open_translationControl m S hS n).choose_spec.1

theorem zero_mem_commonHaarNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) :
    0 ∈ commonHaarNeighborhood m S hS n :=
  (exists_open_translationControl m S hS n).choose_spec.2.1

theorem commonHaarNeighborhood_control
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [Measure.IsAddLeftInvariant m]
    (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i))
    {n i : ℕ} (hi : i ≤ n) {q : Z}
    (hq : q ∈ commonHaarNeighborhood m S hS n) :
    m (((fun z : Z ↦ z + q) ⁻¹' S i) ∆ S i) <
      (2⁻¹ : ℝ≥0∞) ^ (n + 1) :=
  (exists_open_translationControl m S hS n).choose_spec.2.2 i hi q hq

theorem ae_eventually_notMem_haarBadSet_commonHaarNeighborhood
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [m.IsOpenPosMeasure]
    [Measure.IsAddLeftInvariant m]
    (S : ℕ → Set Z) (hS : ∀ i, MeasurableSet (S i)) (i : ℕ) :
    ∀ᵐ z ∂m, ∀ᶠ n : ℕ in atTop,
      z ∉ haarBadSet m (S i) (commonHaarNeighborhood m S hS n) := by
  let badTail : ℕ → Set Z := fun n ↦
    haarBadSet m (S i) (commonHaarNeighborhood m S hS (n + i))
  have hmeasure (n : ℕ) :
      m (badTail n) ≤ 4 * (2⁻¹ : ℝ≥0∞) ^ ((n + i) + 1) := by
    let Q := commonHaarNeighborhood m S hS (n + i)
    have hQopen : IsOpen Q := isOpen_commonHaarNeighborhood m S hS (n + i)
    have hQmeas : MeasurableSet Q := hQopen.measurableSet
    have hQpos : 0 < m Q := hQopen.measure_pos m
      ⟨0, zero_mem_commonHaarNeighborhood m S hS (n + i)⟩
    apply measure_haarBadSet_le m (hS i) hQmeas hQpos
      (by finiteness)
    intro q hq
    exact (commonHaarNeighborhood_control m S hS
      (show i ≤ n + i by omega) hq).le
  have hmeasure' (n : ℕ) :
      m (badTail n) ≤ 4 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
    exact (hmeasure n).trans (mul_le_mul_right
      (pow_le_pow_of_le_one (by simp) (by norm_num)
        (show n + 1 ≤ (n + i) + 1 by omega)) 4)
  have hsumle : (∑' n, m (badTail n)) ≤
      ∑' n : ℕ, 4 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) :=
    ENNReal.tsum_le_tsum hmeasure'
  have hgeom : (∑' n : ℕ, 4 * (2⁻¹ : ℝ≥0∞) ^ (n + 1)) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    apply ENNReal.mul_ne_top
    · norm_num
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.inv_ne_top.mpr (by norm_num)
  have hsum : (∑' n, m (badTail n)) ≠ ∞ :=
    ne_top_of_le_ne_top hgeom hsumle
  filter_upwards [ae_eventually_notMem hsum] with z hz
  rw [eventually_atTop] at hz ⊢
  obtain ⟨N, hN⟩ := hz
  refine ⟨N + i, ?_⟩
  intro j hj
  have hij : i ≤ j := by omega
  have hNj : N ≤ j - i := by omega
  have heq : (j - i) + i = j := by omega
  simpa only [badTail, heq] using hN (j - i) hNj

def conditionalSupportApproxDensitySet
    {Z X : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    (m : Measure Z) (eta : Kernel Z X) (pi : X → Z)
    (Q : ℕ → Set Z) : Set X :=
  {x | ∀ i : ℕ, x ∈ conditionalSupportBasis X i →
    pi x ∈ {z : Z | eta z (conditionalSupportBasis X i) ≠ 0} ∧
      ∀ᶠ n : ℕ in atTop,
        pi x ∉ haarBadSet m
          {z : Z | eta z (conditionalSupportBasis X i) ≠ 0} (Q n)}

theorem measurableSet_conditionalSupportApproxDensitySet
    {Z X : Type*} [MeasurableSpace Z] [AddCommGroup Z]
    [MeasurableAdd₂ Z] [MeasurableNeg Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [SFinite m] (eta : Kernel Z X)
    (pi : X → Z) (hpi : Measurable pi)
    (Q : ℕ → Set Z) (hQ : ∀ n, MeasurableSet (Q n)) :
    MeasurableSet (conditionalSupportApproxDensitySet m eta pi Q) := by
  let B : ℕ → Set X := conditionalSupportBasis X
  let S : ℕ → Set Z := fun i ↦ {z : Z | eta z (B i) ≠ 0}
  have hB (i : ℕ) : MeasurableSet (B i) :=
    (isOpen_conditionalSupportBasis X i).measurableSet
  have hS (i : ℕ) : MeasurableSet (S i) :=
    (eta.measurable_coe (hB i)) (measurableSet_singleton 0).compl
  let E : Set X := ⋂ i : ℕ, (B i)ᶜ ∪
    (pi ⁻¹' S i ∩ ⋃ N : ℕ, ⋂ n : ℕ,
      if N ≤ n then pi ⁻¹' (haarBadSet m (S i) (Q n))ᶜ else Set.univ)
  have hE : MeasurableSet E := by
    apply MeasurableSet.iInter
    intro i
    apply (hB i).compl.union
    apply (hS i).preimage hpi |>.inter
    apply MeasurableSet.iUnion
    intro N
    apply MeasurableSet.iInter
    intro n
    split_ifs
    · exact (measurableSet_haarBadSet m (hS i) (hQ n)).compl.preimage hpi
    · exact MeasurableSet.univ
  convert hE using 1
  ext x
  simp only [E, B, S, conditionalSupportApproxDensitySet,
    Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_iUnion,
    eventually_atTop, Set.mem_ofPred_eq]
  constructor
  · intro hx i
    by_cases hxi : x ∈ conditionalSupportBasis X i
    · right
      refine ⟨(hx i hxi).1, ?_⟩
      obtain ⟨N, hN⟩ := (hx i hxi).2
      exact ⟨N, fun n ↦ by
        by_cases hn : N ≤ n
        · rw [ite_eq_left hn]
          exact hN n hn
        · simp [hn]⟩
    · exact Or.inl hxi
  · intro hx i hxi
    rcases hx i with hnot | hgood
    · exact (hnot hxi).elim
    · refine ⟨hgood.1, ?_⟩
      obtain ⟨N, hN⟩ := hgood.2
      exact ⟨N, fun n hn ↦ by
        simpa only [ite_eq_left hn, Set.mem_compl_iff, Set.mem_preimage] using hN n⟩

theorem ae_mem_conditionalSupportApproxDensitySet
    {Z X : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [m.IsOpenPosMeasure]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z) :
    ∀ᵐ x ∂Measure.bind m eta,
      x ∈ conditionalSupportApproxDensitySet m eta pi
        (commonHaarNeighborhood m
          (fun i ↦ {z : Z | eta z (conditionalSupportBasis X i) ≠ 0})
          (fun i ↦ (eta.measurable_coe
            (isOpen_conditionalSupportBasis X i).measurableSet)
              (measurableSet_singleton 0).compl)) := by
  let B : ℕ → Set X := conditionalSupportBasis X
  let S : ℕ → Set Z := fun i ↦ {z : Z | eta z (B i) ≠ 0}
  have hB (i : ℕ) : MeasurableSet (B i) :=
    (isOpen_conditionalSupportBasis X i).measurableSet
  have hS (i : ℕ) : MeasurableSet (S i) :=
    (eta.measurable_coe (hB i)) (measurableSet_singleton 0).compl
  let Q : ℕ → Set Z := commonHaarNeighborhood m S hS
  have hbase : ∀ᵐ z ∂m, ∀ i,
      ∀ᶠ n : ℕ in atTop, z ∉ haarBadSet m (S i) (Q n) := by
    apply ae_all_iff.mpr
    intro i
    exact ae_eventually_notMem_haarBadSet_commonHaarNeighborhood m S hS i
  have hcond : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z,
      ∀ i, x ∈ B i → z ∈ S i ∧
        ∀ᶠ n : ℕ in atTop, z ∉ haarBadSet m (S i) (Q n) := by
    filter_upwards [hbase, hfiber] with z hz hzpi
    apply ae_all_iff.mpr
    intro i
    by_cases hzS : z ∈ S i
    · filter_upwards [hzpi] with x hxpi
      intro _
      exact ⟨hzS, hz i⟩
    · have hzero : eta z (B i) = 0 := not_ne_iff.mp hzS
      have hnotB : ∀ᵐ x ∂eta z, x ∉ B i := by
        rw [ae_iff]
        have heq : {x : X | ¬x ∉ B i} = B i := by ext x; simp
        rw [heq]
        exact hzero
      filter_upwards [hnotB] with x hx
      exact fun hxB ↦ (hx hxB).elim
  have hpiece : MeasurableSet
      (conditionalSupportApproxDensitySet m eta pi Q) := by
    apply measurableSet_conditionalSupportApproxDensitySet m eta pi hpi Q
    intro n
    exact (isOpen_commonHaarNeighborhood m S hS n).measurableSet
  apply Measure.ae_comp_of_ae_ae hpiece
  filter_upwards [hcond, hfiber] with z hz hzpi
  filter_upwards [hz, hzpi] with x hx hxpi
  intro i hxi
  simpa only [Q, S, B, hxpi, Set.mem_ofPred_eq] using hx i hxi

theorem hasConditionalSupportDensityAlong_approximateIdentity
    {Z X : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [m.IsOpenPosMeasure]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) :
    let S : ℕ → Set Z := fun i ↦
      {z : Z | eta z (conditionalSupportBasis X i) ≠ 0}
    let hS : ∀ i, MeasurableSet (S i) := fun i ↦
      (eta.measurable_coe
        (isOpen_conditionalSupportBasis X i).measurableSet)
          (measurableSet_singleton 0).compl
    let Q : ℕ → Set Z := commonHaarNeighborhood m S hS
    HasConditionalSupportDensityAlong m eta pi
      (conditionalSupportApproxDensitySet m eta pi Q) Q := by
  dsimp only
  let S : ℕ → Set Z := fun i ↦
    {z : Z | eta z (conditionalSupportBasis X i) ≠ 0}
  have hS (i : ℕ) : MeasurableSet (S i) :=
    (eta.measurable_coe
      (isOpen_conditionalSupportBasis X i).measurableSet)
        (measurableSet_singleton 0).compl
  let Q : ℕ → Set Z := commonHaarNeighborhood m S hS
  constructor
  · intro n
    have hQopen : IsOpen (Q n) := isOpen_commonHaarNeighborhood m S hS n
    refine ⟨hQopen.measurableSet, ?_⟩
    exact ENNReal.toReal_pos
      (hQopen.measure_pos m
        ⟨0, zero_mem_commonHaarNeighborhood m S hS n⟩).ne'
      (measure_ne_top m _)
  · intro x hx U hUopen hxU
    obtain ⟨V, hVB, hxV, hVU⟩ :=
      (conditionalSupportBasis_isBasis X).exists_subset_of_mem_open hxU hUopen
    rcases hVB with ⟨i, rfl⟩
    have hxdata := hx i hxV
    filter_upwards [hxdata.2] with n hn
    let num := m (S i ∩ leftAddTranslate (pi x) (Q n))
    let q := m (Q n)
    have hnotle : ¬(4 : ℝ≥0∞) * num ≤ (3 : ℝ≥0∞) * q := by
      intro hle
      apply hn
      exact ⟨hxdata.1, hle⟩
    have hlt : (3 : ℝ≥0∞) * q < (4 : ℝ≥0∞) * num := lt_of_not_ge hnotle
    have hfiniteNum : num ≠ ∞ := measure_ne_top m _
    have hfiniteQ : q ≠ ∞ := measure_ne_top m _
    have hltR := (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by norm_num) hfiniteQ)
      (ENNReal.mul_ne_top (by norm_num) hfiniteNum)).mpr hlt
    have hbasis : (3 / 4 : ℝ) * m.real (Q n) <
        m.real (S i ∩ leftAddTranslate (pi x) (Q n)) := by
      dsimp only [num, q] at hltR
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hltR
      change (3 / 4 : ℝ) * (m (Q n)).toReal <
        (m (S i ∩ leftAddTranslate (pi x) (Q n))).toReal
      calc
        (3 / 4 : ℝ) * (m (Q n)).toReal =
            (3 * (m (Q n)).toReal) / 4 := by ring
        _ < (4 * (m (S i ∩ leftAddTranslate (pi x) (Q n))).toReal) / 4 :=
          div_lt_div_of_pos_right hltR (by norm_num)
        _ = (m (S i ∩ leftAddTranslate (pi x) (Q n))).toReal := by ring
    apply hbasis.trans_le
    apply measureReal_mono
    · rintro z ⟨hz, hzQ⟩
      refine ⟨?_, hzQ⟩
      intro hzero
      exact hz (measure_mono_null hVU hzero)
    · exact measure_ne_top m _

theorem conditionalSupportOverlap_of_fiberApproximateIdentity
    {Z X : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [T2Space Z] [SecondCountableTopology Z] [CompactSpace Z]
    [AddCommGroup Z] [IsTopologicalAddGroup Z] [MeasurableEq Z]
    [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure Z) [IsProbabilityMeasure m]
    [IsLocallyFiniteMeasure m] [m.IsOpenPosMeasure]
    [Measure.IsAddLeftInvariant m]
    (eta : Kernel Z X) (pi : X → Z) (hpi : Measurable pi)
    (hfiber : ∀ᵐ z ∂m, ∀ᵐ x ∂eta z, pi x = z)
    (sigma : Measure (X × X))
    (hfst : Measure.map Prod.fst sigma = Measure.bind m eta)
    (hsnd : Measure.map Prod.snd sigma ≪ Measure.bind m eta) :
    HasConditionalSupportOverlap m eta pi sigma := by
  let S : ℕ → Set Z := fun i ↦
    {z : Z | eta z (conditionalSupportBasis X i) ≠ 0}
  have hS (i : ℕ) : MeasurableSet (S i) :=
    (eta.measurable_coe
      (isOpen_conditionalSupportBasis X i).measurableSet)
        (measurableSet_singleton 0).compl
  let Q : ℕ → Set Z := commonHaarNeighborhood m S hS
  let L : Set X := conditionalSupportApproxDensitySet m eta pi Q
  exact ae_conditionalSupportOverlap_of_densityAlong
    m eta pi (Measure.bind m eta) L Q sigma
      (hasConditionalSupportDensityAlong_approximateIdentity m eta pi)
      (ae_mem_conditionalSupportApproxDensitySet m eta pi hpi hfiber)
      hfst hsnd

end Erdos656

namespace Erdos656

open Filter Function Set Topology MeasureTheory
open ProbabilityTheory
open scoped ENNReal Pointwise Topology

/-- The relative-product component is invariant under the diagonal graph
extension: both compact-factor coordinates are translated by the same
rotation. -/
theorem factorComponent_kroneckerGraph_invariant
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X] [StandardBorelSpace X] [Nonempty X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [MeasurableAdd₂ (KroneckerSubgroup e mu he.toMeasurePreserving)]
    [MeasurableNeg (KroneckerSubgroup e mu he.toMeasurePreserving)]
    [Measure.IsAddLeftInvariant (kroneckerFactorMeasure e mu he)] :
    ∀ p : KroneckerGraphSpace e mu he × KroneckerGraphSpace e mu he,
      factorComponent (kroneckerFactorMeasure e mu he)
          (kroneckerGraphFiberKernel e mu he) Prod.snd
          (diagonalTransform (kroneckerGraphMeasurableEquiv e mu he) p) =
        factorComponent (kroneckerFactorMeasure e mu he)
          (kroneckerGraphFiberKernel e mu he) Prod.snd p := by
  intro p
  apply factorComponent_eq_of_difference_eq
    (kroneckerFactorMeasure e mu he)
    (kroneckerGraphFiberKernel e mu he) Prod.snd
  simp only [diagonalTransform_apply, kroneckerGraphMeasurableEquiv_apply]
  abel

/-- Projecting a graph-extension Erdős progression to its original-space
coordinate gives an Erdős progression in the original system. -/
theorem IsErdosProgression.kroneckerGraph_fst
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace.CountablyGenerated X]
    (e : X ≃ᵐ X) (mu : Measure X) [IsProbabilityMeasure mu]
    (he : Ergodic e mu)
    [SecondCountableTopology (KroneckerSubgroup e mu he.toMeasurePreserving)]
    {a q₁ q₂ : KroneckerGraphSpace e mu he}
    (h : IsErdosProgression (kroneckerGraphMeasurableEquiv e mu he) a q₁ q₂) :
    IsErdosProgression e a.1 q₁.1 q₂.1 := by
  obtain ⟨c, hc, hlim⟩ := h
  refine ⟨c, hc, ?_⟩
  let P : (KroneckerGraphSpace e mu he × KroneckerGraphSpace e mu he) → X × X :=
    fun p ↦ (p.1.1, p.2.1)
  have hP : Continuous P := continuous_fst.comp continuous_fst |>.prodMk
    (continuous_fst.comp continuous_snd)
  have hmapped := hP.continuousAt.tendsto.comp hlim
  have hE : (kroneckerGraphMeasurableEquiv e mu he :
      KroneckerGraphSpace e mu he → KroneckerGraphSpace e mu he) =
      kroneckerGraphTransform e mu he := by
    funext p
    rfl
  rw [hE] at hmapped
  have hsource :
      (P ∘ fun n ↦
        ((kroneckerGraphTransform e mu he)^[c n] a,
          (kroneckerGraphTransform e mu he)^[c n] q₁)) =
        (fun n ↦ (e^[c n] a.1, e^[c n] q₁.1)) := by
    funext n
    simp only [P, Function.comp_apply, kroneckerGraphTransform_iterate_apply]
  rw [hsource] at hmapped
  exact hmapped

/-- Erdős Problem 656: every set of natural numbers of positive upper
density contains an infinite set whose restricted pair sums, after one
integer translate, all return to the original set. -/
theorem erdos_656 {A : Set ℕ} (hA : HasPositiveUpperDensity A) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      HasTranslatedRestrictedPairSums A B := by
  obtain ⟨mu, baseStart, baseLength, hmuErgodic, hmuOrigin, hbaseGeneric⟩ :=
    exists_pointed_ergodic_intervalGeneric hA
  let e : SymbolicSpace ≃ᵐ SymbolicSpace :=
    symbolicShiftHomeomorph.toMeasurableEquiv
  have he : Ergodic e (mu : Measure SymbolicSpace) := by
    change Ergodic symbolicShift (mu : Measure SymbolicSpace)
    exact hmuErgodic
  have heContinuous : Continuous (e : SymbolicSpace → SymbolicSpace) := by
    change Continuous symbolicShift
    exact continuous_symbolicShift
  have hbaseGeneric' : IsGenericAlongOrbitIntervals e (symbolicPoint A)
      (mu : Measure SymbolicSpace) baseStart baseLength := by
    change IsGenericAlongOrbitIntervals symbolicShift (symbolicPoint A)
      (mu : Measure SymbolicSpace) baseStart baseLength
    exact hbaseGeneric
  have haSupportGeneric : IsSupportGeneric
      (fun n ↦ e^[n] (symbolicPoint A)) (mu : Measure SymbolicSpace) :=
    supportGeneric_of_genericAlongOrbitIntervals e (symbolicPoint A)
      (mu : Measure SymbolicSpace) baseStart baseLength hbaseGeneric'
  let : PseudoMetricSpace SymbolicSpace :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric SymbolicSpace
  let : Countable (KoopmanEigenvalueType e (mu : Measure SymbolicSpace)
      he.toMeasurePreserving) :=
    (countable_koopmanEigenvalues e (mu : Measure SymbolicSpace)
      he.toMeasurePreserving).to_subtype
  let H := KroneckerSubgroup e (mu : Measure SymbolicSpace)
    he.toMeasurePreserving
  let : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let : BorelSpace H := inferInstance
  let : PseudoMetricSpace H :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric H
  let : MeasurableAdd₂ H := ContinuousAdd.measurableMul₂
  let : MeasurableNeg H := inferInstance
  let : MeasurableEq H := inferInstance
  let m := kroneckerFactorMeasure e (mu : Measure SymbolicSpace) he
  let eta := kroneckerGraphFiberKernel e (mu : Measure SymbolicSpace) he
  let Q := KroneckerGraphSpace e (mu : Measure SymbolicSpace) he
  let E := kroneckerGraphMeasurableEquiv e (mu : Measure SymbolicSpace) he
  let : Measure.IsAddHaarMeasure m :=
    isAddHaarMeasure_kroneckerFactorMeasure e (mu : Measure SymbolicSpace) he
  obtain ⟨z, graphStart, graphLength, hgraphGeneric⟩ :=
    exists_pointed_kroneckerGraph_intervalGeneric e
      (mu : Measure SymbolicSpace) he heContinuous (symbolicPoint A)
      haSupportGeneric
  let aQ : Q := (symbolicPoint A, z)
  have hEeq : (E : Q → Q) =
      kroneckerGraphTransform e (mu : Measure SymbolicSpace) he := by
    funext q
    rfl
  have hEContinuous : Continuous (E : Q → Q) := by
    rw [hEeq]
    exact continuous_kroneckerGraphTransform e (mu : Measure SymbolicSpace)
      he heContinuous
  have hgraphGeneric' : IsGenericAlongOrbitIntervals E aQ
      (kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he)
      graphStart graphLength := by
    rw [hEeq]
    exact hgraphGeneric
  have haQSupportGenericGraph : IsSupportGeneric
      (fun n ↦ E^[n] aQ)
      (kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he) :=
    supportGeneric_of_genericAlongOrbitIntervals E aQ
      (kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he)
      graphStart graphLength hgraphGeneric'
  have haQSupportGeneric : IsSupportGeneric
      (fun n ↦ E^[n] aQ) (Measure.bind m eta) := by
    rw [show Measure.bind m eta =
        kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he by
      simpa only [m, eta] using
        bind_kroneckerGraphFiberKernel e (mu : Measure SymbolicSpace) he]
    exact haQSupportGenericGraph
  have hfiber : ∀ᵐ w ∂m, ∀ᵐ q ∂eta w, Prod.snd q = w := by
    simpa only [m, eta] using
      kroneckerGraphFiberKernel_fiber e (mu : Measure SymbolicSpace) he
  have hdouble : Measure.map (fun w : H ↦ Prod.snd aQ + w + w) m ≪ m := by
    simpa only [m, aQ, add_assoc] using
      (map_add_left_double_absolutelyContinuous m
        (kroneckerSubgroupRotation e (mu : Measure SymbolicSpace) he) z
        (ergodic_kroneckerSubgroupRotation e (mu : Measure SymbolicSpace) he))
  have hcontinuousComponent : Continuous (factorComponent m eta Prod.snd) :=
    continuous_factorComponent m eta Prod.snd continuous_snd
  have hinvariantComponent : ∀ p : Q × Q,
      factorComponent m eta Prod.snd (diagonalTransform E p) =
        factorComponent m eta Prod.snd p := by
    simpa only [m, eta, E, Q] using
      (factorComponent_kroneckerGraph_invariant e
        (mu : Measure SymbolicSpace) he)
  have hgenericComponent :=
    exists_kroneckerGraph_generic_component e (mu : Measure SymbolicSpace) he
  have hfst : Measure.map Prod.fst
      (progressionProbability m eta (Prod.snd aQ) : Measure (Q × Q)) =
      Measure.bind m eta :=
    fst_progressionProbability_eq_base m eta (Prod.snd aQ)
  have hsnd : Measure.map Prod.snd
      (progressionProbability m eta (Prod.snd aQ) : Measure (Q × Q)) ≪
      Measure.bind m eta :=
    snd_progressionProbability_ac_base m eta (Prod.snd aQ) hdouble
  have hsupportOverlap : HasConditionalSupportOverlap m eta Prod.snd
      (progressionProbability m eta (Prod.snd aQ) : Measure (Q × Q)) :=
    conditionalSupportOverlap_of_fiberApproximateIdentity m eta Prod.snd
      measurable_snd hfiber
      (progressionProbability m eta (Prod.snd aQ) : Measure (Q × Q))
      hfst hsnd
  have hdata : ContinuousKroneckerKMRRData E m eta Prod.snd aQ := by
    exact ⟨measurable_snd, hfiber, hdouble, hcontinuousComponent,
      hinvariantComponent, hgenericComponent, hsupportOverlap⟩
  let D := hdata.toContinuousKMRRDecomposition E m eta Prod.snd aQ
  have hjoin : IsAbstractKMRRJoining E aQ (Measure.bind m eta)
      (D.sigma : Measure (Q × Q))
      (fun p ↦ (D.component p : Measure (Q × Q))) := by
    exact D.isAbstractKMRRJoining E hEContinuous aQ (Measure.bind m eta)
      (measurePreserving_kroneckerGraphBind e (mu : Measure SymbolicSpace) he)
      haQSupportGeneric
  have hprogression : ∀ᵐ p ∂(D.sigma : Measure (Q × Q)),
      IsErdosProgression E aQ p.1 p.2 := by
    filter_upwards [hjoin.2.2] with p hp
    exact isErdosProgression_of_supportGeneric E aQ p.1 p.2
      (D.component p : Measure (Q × Q)) hp.1 hp.2
  have hmuSaturation : ∀ᵐ x ∂(mu : Measure SymbolicSpace),
      x ∈ ⋃ t : ℕ, shiftedOriginCylinder t := by
    rw [← forwardSaturation_originCylinder]
    exact ae_mem_forwardSaturation_of_ergodic hmuErgodic
      isClopen_originCylinder.isOpen.measurableSet (ne_of_gt hmuOrigin)
  have hgraphSaturation : ∀ᵐ q ∂Measure.bind m eta,
      q.1 ∈ ⋃ t : ℕ, shiftedOriginCylinder t := by
    have hmap : ∀ᵐ x ∂Measure.map Prod.fst (Measure.bind m eta),
        x ∈ ⋃ t : ℕ, shiftedOriginCylinder t := by
      rw [show Measure.bind m eta =
          kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he by
        simpa only [m, eta] using
          bind_kroneckerGraphFiberKernel e (mu : Measure SymbolicSpace) he]
      rw [map_fst_kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he]
      exact hmuSaturation
    exact ae_of_ae_map measurable_fst.aemeasurable hmap
  have hsaturationMap : ∀ᵐ q ∂Measure.map Prod.snd
      (D.sigma : Measure (Q × Q)),
      q.1 ∈ ⋃ t : ℕ, shiftedOriginCylinder t :=
    hjoin.2.1.ae_le hgraphSaturation
  have hsaturationPair : ∀ᵐ p ∂(D.sigma : Measure (Q × Q)),
      p.2.1 ∈ ⋃ t : ℕ, shiftedOriginCylinder t :=
    ae_of_ae_map measurable_snd.aemeasurable hsaturationMap
  let F : Set (Q × Q) := {p | p.1.1 ∈ originCylinder}
  have hF : MeasurableSet F := by
    exact isClopen_originCylinder.isOpen.measurableSet.preimage
      (measurable_fst.comp measurable_fst)
  have hbaseSet : MeasurableSet (Prod.fst ⁻¹' originCylinder : Set Q) :=
    isClopen_originCylinder.isOpen.measurableSet.preimage measurable_fst
  have hsigmaF : 0 < (D.sigma : Measure (Q × Q)) F := by
    calc
      0 < (mu : Measure SymbolicSpace) originCylinder := hmuOrigin
      _ = Measure.map Prod.fst
          (kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he)
          originCylinder := by
        rw [map_fst_kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he]
      _ = (kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he)
          (Prod.fst ⁻¹' originCylinder) := by
        rw [Measure.map_apply measurable_fst
          isClopen_originCylinder.isOpen.measurableSet]
      _ = Measure.bind m eta (Prod.fst ⁻¹' originCylinder) := by
        rw [show Measure.bind m eta =
            kroneckerGraphMeasure e (mu : Measure SymbolicSpace) he by
          simpa only [m, eta] using
            bind_kroneckerGraphFiberKernel e (mu : Measure SymbolicSpace) he]
      _ = Measure.map Prod.fst (D.sigma : Measure (Q × Q))
          (Prod.fst ⁻¹' originCylinder) := by rw [hjoin.1]
      _ = (D.sigma : Measure (Q × Q)) F := by
        rw [Measure.map_apply measurable_fst hbaseSet]
        rfl
  let : NeBot (ae ((D.sigma : Measure (Q × Q)).restrict F)) :=
    ae_restrict_neBot.mpr (ne_of_gt hsigmaF)
  have hmem : ∀ᵐ p ∂(D.sigma : Measure (Q × Q)).restrict F, p ∈ F :=
    ae_restrict_mem hF
  have hprogressionRestrict :
      ∀ᵐ p ∂(D.sigma : Measure (Q × Q)).restrict F,
        IsErdosProgression E aQ p.1 p.2 :=
    ae_restrict_of_ae hprogression
  have hsaturationRestrict :
      ∀ᵐ p ∂(D.sigma : Measure (Q × Q)).restrict F,
        p.2.1 ∈ ⋃ t : ℕ, shiftedOriginCylinder t :=
    ae_restrict_of_ae hsaturationPair
  obtain ⟨p, hpF, hpProgression, hpSaturation⟩ :=
    (hmem.and (hprogressionRestrict.and hsaturationRestrict)).exists
  obtain ⟨t, hpt⟩ := Set.mem_iUnion.mp hpSaturation
  have hpProjected : IsErdosProgression symbolicShift (symbolicPoint A)
      p.1.1 p.2.1 := by
    have hp' := hpProgression.kroneckerGraph_fst e
      (mu : Measure SymbolicSpace) he
    change IsErdosProgression symbolicShift (symbolicPoint A) p.1.1 p.2.1 at hp'
    exact hp'
  exact conclusion_of_pointedProgression
    ⟨t, p.1.1, p.2.1, hpF, hpt, hpProjected⟩

end Erdos656

alias _root_.Erdos656.erdos656 := _root_.Erdos656.erdos_656
