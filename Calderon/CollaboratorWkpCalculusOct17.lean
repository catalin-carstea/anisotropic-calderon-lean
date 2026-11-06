import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! Coordinate differentiation `W^{k+1,2}(Ω) → W^{k,2}(Ω)` and reconstruction of a Sobolev
function from its coordinate partial derivatives, on open subsets of `R3`.

Tau Ceti stores the higher weak derivatives of `u` as nested linear maps whose innermost slot is
the gradient vector and whose new derivative directions are added on the left.  The higher
derivatives of `∂ᵢ u` are therefore obtained by contracting the innermost slot with `eᵢ`, and no
symmetry of mixed weak derivatives is needed. -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.WkpCalculus

open TauCeti

/-- The standard basis vector `eᵢ` of `R3`. -/
@[inline, reducible] def e (i : Fin 3) : R3 := EuclideanSpace.single i 1

/-! ### Contraction of the innermost slot -/

/-- `contr i j` maps an iterated-gradient field with `j + 1` added directions to one with `j`,
by pairing the innermost (gradient) slot with `eᵢ` and re-identifying the last direction as the
new gradient slot. -/
def contr (i : Fin 3) : (j : ℕ) → IteratedGradient R3 (j + 1) →L[ℝ] IteratedGradient R3 j
  | 0 => ∑ m : Fin 3,
      (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).comp
        (ContinuousLinearMap.apply ℝ R3 (e m))).smulRight (e m))
  | j + 1 => ContinuousLinearMap.compL ℝ R3 (IteratedGradient R3 (j + 1))
      (IteratedGradient R3 j) (contr i j)

theorem contr_succ_apply (i : Fin 3) (j : ℕ) (T : IteratedGradient R3 (j + 2)) (v : R3) :
    contr i (j + 1) T v = contr i j (T v) := rfl

theorem innerSL_contr_zero (i : Fin 3) (T : R3 →L[ℝ] R3) :
    innerSL ℝ (contr i 0 T) =
      (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).comp T := by
  refine ContinuousLinearMap.ext fun (v : R3) => ?_
  simp only [contr, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, sum_inner, inner_smul_left]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ContinuousLinearMap.apply_apply, EuclideanSpace.inner_single_left]
  simp [mul_comm]


/-- Weak Fréchet differentiation commutes with a continuous linear map on the codomain. -/
theorem hasWeakFDerivOn_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {Ω : Opens R3}
    {u : R3 → F} {U : R3 → R3 →L[ℝ] F} (h : HasWeakFDerivOn volume Ω u U) (L : F →L[ℝ] G) :
    HasWeakFDerivOn volume Ω (fun x => L (u x)) (fun x => L.comp (U x)) :=
  hasWeakFDerivOn_iff.mpr fun v => ((hasWeakFDerivOn_iff.mp h v).clm_comp L)

variable {Ω : Opens R3}

/-! ### Coordinate differentiation -/

/-- `∂ᵢ` at the bottom order: the `i`th coordinate of the weak gradient. -/
def d0 (i : Fin 3) (u : Wkp (volume : Measure R3) Ω 2 1) : Wkp (volume : Measure R3) Ω 2 0 :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).compLp (Wkp.iteratedGradient 0 u)

/-- `∂ᵢ : W^{2} → W^{1}`. -/
def d1 (i : Fin 3) (w : Wkp (volume : Measure R3) Ω 2 2) : W1p (volume : Measure R3) Ω 2 :=
  W1p.mk (d0 i (Wkp.lowerOrder 1 w)) ((contr i 0).compLp (Wkp.iteratedGradient 1 w)) (by
    have h := hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_iteratedGradient 0 w)
      (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)
    refine (h.congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [ContinuousLinearMap.coeFn_compLp (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)
        (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w))] with x hx
      exact hx.symm
    · filter_upwards [ContinuousLinearMap.coeFn_compLp (contr i 0)
        (Wkp.iteratedGradient 1 w)] with x hx
      rw [hx, innerSL_contr_zero])

theorem value_d1 (i : Fin 3) (w : Wkp (volume : Measure R3) Ω 2 2) :
    W1p.value (d1 i w) = d0 i (Wkp.lowerOrder 1 w) := W1p.value_mk _ _ _

theorem gradient_d1 (i : Fin 3) (w : Wkp (volume : Measure R3) Ω 2 2) :
    W1p.gradient (d1 i w) = (contr i 0).compLp (Wkp.iteratedGradient 1 w) := W1p.gradient_mk _ _ _

theorem dPack_hasWeakFDerivOn (i : Fin 3) (k : ℕ) (w : Wkp (volume : Measure R3) Ω 2 (k + 3))
    {v : Wkp (volume : Measure R3) Ω 2 (k + 1)}
    (hv : ⇑(Wkp.iteratedGradient k v) =ᵐ[(volume : Measure R3).restrict Ω]
        fun x => contr i k (Wkp.iteratedGradient (k + 1) (Wkp.lowerOrder (k + 2) w) x)) :
    HasWeakFDerivOn volume Ω (Wkp.iteratedGradient k v)
      ((contr i (k + 1)).compLp (Wkp.iteratedGradient (k + 2) w)) := by
  have h := hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_iteratedGradient (k + 1) w)
    (contr i k)
  refine (h.congr_ae hv.symm).congr_ae_deriv ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (contr i (k + 1))
    (Wkp.iteratedGradient (k + 2) w)] with x hx
  rw [hx]
  rfl

/-- `∂ᵢ : W^{k+2} → W^{k+1}`, bundled with the identification of its top derivative field. -/
def dPack (i : Fin 3) : (k : ℕ) → (w : Wkp (volume : Measure R3) Ω 2 (k + 2)) →
    {v : Wkp (volume : Measure R3) Ω 2 (k + 1) //
      ⇑(Wkp.iteratedGradient k v) =ᵐ[(volume : Measure R3).restrict Ω]
        fun x => contr i k (Wkp.iteratedGradient (k + 1) w x)}
  | 0, w => ⟨(d1 i w : Wkp (volume : Measure R3) Ω 2 1), by
      have h := Wkp.iteratedGradient_zero (d1 i w : Wkp (volume : Measure R3) Ω 2 1)
      rw [h]
      erw [gradient_d1]
      exact ContinuousLinearMap.coeFn_compLp _ _⟩
  | k + 1, w =>
    ⟨Wkp.mk k (dPack i k (Wkp.lowerOrder (k + 2) w)).1
        ((contr i (k + 1)).compLp (Wkp.iteratedGradient (k + 2) w))
        (dPack_hasWeakFDerivOn i k w (dPack i k (Wkp.lowerOrder (k + 2) w)).2), by
      rw [Wkp.iteratedGradient_mk]
      exact ContinuousLinearMap.coeFn_compLp _ _⟩

/-- Coordinate differentiation `∂ᵢ : W^{k+1,2}(Ω) → W^{k,2}(Ω)`. -/
def d (i : Fin 3) : (k : ℕ) → Wkp (volume : Measure R3) Ω 2 (k + 1) →
    Wkp (volume : Measure R3) Ω 2 k
  | 0, u => d0 i u
  | k + 1, u => (dPack i k u).1


theorem d_succ (i : Fin 3) (k : ℕ) (u : Wkp (volume : Measure R3) Ω 2 (k + 2)) :
    d i (k + 1) u = (dPack i k u).1 := rfl

/-- Forgetting the top derivative commutes with `∂ᵢ`. -/
theorem lowerOrder_d (i : Fin 3) : ∀ (k : ℕ) (u : Wkp (volume : Measure R3) Ω 2 (k + 2)),
    Wkp.lowerOrder k (d i (k + 1) u) = d i k (Wkp.lowerOrder (k + 1) u)
  | 0, u => by
      rw [d_succ]
      exact (Wkp.lowerOrder_zero (d1 i u : Wkp (volume : Measure R3) Ω 2 1)).trans
        (value_d1 i u)
  | k + 1, u => by
      show Wkp.lowerOrder (k + 1) (dPack i (k + 1) u).1 = (dPack i k (Wkp.lowerOrder (k + 2) u)).1
      rw [dPack]
      exact Wkp.lowerOrder_mk _ _ _ (dPack_hasWeakFDerivOn i k u (dPack i k _).2)

/-- The top derivative field of `∂ᵢ u` is the contracted top derivative field of `u`. -/
theorem iteratedGradient_d (i : Fin 3) (k : ℕ) (u : Wkp (volume : Measure R3) Ω 2 (k + 2)) :
    Wkp.iteratedGradient k (d i (k + 1) u) =
      (contr i k).compLp (Wkp.iteratedGradient (k + 1) u) := by
  apply Lp.ext
  filter_upwards [(dPack i k u).2, ContinuousLinearMap.coeFn_compLp (contr i k)
    (Wkp.iteratedGradient (k + 1) u)] with x h1 h2
  rw [d_succ, h1, h2]

/-- The value of `∂ᵢ u` is the `i`th coordinate of the weak gradient of `u`. -/
theorem value_d (i : Fin 3) : ∀ (k : ℕ) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)),
    ⇑(Wkp.value k (d i k u)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient (Wkp.firstOrder k u) x i
  | 0, u => by
      rw [Wkp.value_zero, Wkp.firstOrder_zero]
      filter_upwards [ContinuousLinearMap.coeFn_compLp (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)
        (Wkp.iteratedGradient 0 u)] with x hx
      rw [d, d0, hx, Wkp.iteratedGradient_zero]
      rfl
  | k + 1, u => by
      rw [Wkp.value_succ, lowerOrder_d, Wkp.firstOrder_succ]
      exact value_d i k _

theorem d_add (i : Fin 3) (k : ℕ) (u v : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    d i k (u + v) = d i k u + d i k v := by
  apply Wkp.ext k
  rw [Wkp.value_add]
  apply Lp.ext
  have hg : W1p.gradient (Wkp.firstOrder k (u + v)) =
      W1p.gradient (Wkp.firstOrder k u) + W1p.gradient (Wkp.firstOrder k v) := by
    simp only [← Wkp.firstOrderL_apply, ← W1p.gradientL_apply, map_add]
  filter_upwards [value_d i k (u + v), value_d i k u, value_d i k v,
    Lp.coeFn_add (Wkp.value k (d i k u)) (Wkp.value k (d i k v)),
    Lp.coeFn_add (W1p.gradient (Wkp.firstOrder k u)) (W1p.gradient (Wkp.firstOrder k v))]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, hg, h5, Pi.add_apply]
  rfl

theorem d_smul (i : Fin 3) (k : ℕ) (c : ℝ) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    d i k (c • u) = c • d i k u := by
  apply Wkp.ext k
  rw [Wkp.value_smul]
  apply Lp.ext
  have hg : W1p.gradient (Wkp.firstOrder k (c • u)) = c • W1p.gradient (Wkp.firstOrder k u) := by
    simp only [← Wkp.firstOrderL_apply, ← W1p.gradientL_apply, map_smul]
  filter_upwards [value_d i k (c • u), value_d i k u,
    Lp.coeFn_smul c (Wkp.value k (d i k u)),
    Lp.coeFn_smul c (W1p.gradient (Wkp.firstOrder k u))] with x h1 h2 h4 h5
  rw [h1, h4, Pi.smul_apply, h2, hg, h5, Pi.smul_apply]
  rfl

theorem continuous_d (i : Fin 3) : ∀ k : ℕ,
    Continuous (d (Ω := Ω) i k)
  | 0 => ((ContinuousLinearMap.compLpL 2 _ (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)).continuous.comp
      (Wkp.iteratedGradientL 0).continuous)
  | k + 1 => by
      rw [Wkp.continuous_iff_lowerOrder_iteratedGradient]
      constructor
      · simp only [lowerOrder_d]
        exact (continuous_d i k).comp (Wkp.lowerOrderL (k + 1)).continuous
      · simp only [iteratedGradient_d]
        exact (ContinuousLinearMap.compLpL 2 _ (contr i k)).continuous.comp
          (Wkp.iteratedGradientL (k + 1)).continuous

/-- Coordinate differentiation as a continuous linear operator. -/
def dL (i : Fin 3) (k : ℕ) :
    Wkp (volume : Measure R3) Ω 2 (k + 1) →L[ℝ] Wkp (volume : Measure R3) Ω 2 k where
  toFun := d i k
  map_add' := d_add i k
  map_smul' := d_smul i k
  cont := continuous_d i k

theorem dL_apply (i : Fin 3) (k : ℕ) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    dL i k u = d i k u := rfl


/-! ### Reconstruction from coordinate partial derivatives -/

/-- `lift i j` places a field with `j` added directions as the `eᵢ` component of the innermost
slot of a field with `j + 1` added directions; at `j = 0`, `s ↦ (v ↦ ⟪s, v⟫ eᵢ)`. -/
def lift (i : Fin 3) : (j : ℕ) → IteratedGradient R3 j →L[ℝ] IteratedGradient R3 (j + 1)
  | 0 => (ContinuousLinearMap.compL ℝ R3 ℝ R3
      (ContinuousLinearMap.toSpanSingleton ℝ (e i))).comp (innerSL ℝ)
  | j + 1 => ContinuousLinearMap.compL ℝ R3 (IteratedGradient R3 j)
      (IteratedGradient R3 (j + 1)) (lift i j)

theorem norm_lift_le (i : Fin 3) : ∀ j : ℕ, ‖lift i j‖ ≤ 1
  | 0 => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun (s : R3) => by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun (v : R3) => ?_
      change ‖(inner ℝ s v) • e i‖ ≤ ‖s‖ * ‖v‖
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      exact abs_real_inner_le_norm s v
  | j + 1 => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => by
      change ‖(lift i j).comp T‖ ≤ 1 * ‖T‖
      have := norm_lift_le i j
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right this (norm_nonneg _))

/-- Weak Fréchet differentiation commutes with finite sums. -/
theorem hasWeakFDerivOn_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {ι : Type*} (s : Finset ι) {u : ι → R3 → F} {U : ι → R3 → R3 →L[ℝ] F}
    (h : ∀ i ∈ s, HasWeakFDerivOn volume Ω (u i) (U i)) :
    HasWeakFDerivOn volume Ω (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, U i x) := by
  refine hasWeakFDerivOn_iff.mpr fun v => ?_
  have := HasWeakLineDerivOn.sum (v := v) s fun i hi => hasWeakFDerivOn_iff.mp (h i hi) v
  simpa only [FunLike.coe_sum, Finset.sum_apply] using this

/-- The top derivative field of the function reconstructed from partial derivatives `g`. -/
def topField : (k : ℕ) → (Fin 3 → Wkp (volume : Measure R3) Ω 2 k) → R3 → IteratedGradient R3 k
  | 0, g => fun x => ∑ i, Wkp.value 0 (g i) x • e i
  | k + 1, g => fun x => ∑ i, lift i k (Wkp.iteratedGradient k (g i) x)

theorem hasWeakFDerivOn_topField : ∀ (k : ℕ) (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 (k + 1)),
    HasWeakFDerivOn volume Ω (topField k fun i => Wkp.lowerOrder k (g i))
      (fun x => ∑ i, lift i k (Wkp.iteratedGradient k (g i) x))
  | 0, g => by
      refine hasWeakFDerivOn_sum Finset.univ fun i _ => ?_
      exact hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_value (g i))
        (ContinuousLinearMap.toSpanSingleton ℝ (e i))
  | k + 1, g => by
      refine hasWeakFDerivOn_sum Finset.univ fun i _ => ?_
      exact hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_iteratedGradient k (g i)) (lift i k)

theorem ofPartials_hasWeakFDerivOn (k : ℕ) (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 (k + 1))
    {U : Wkp (volume : Measure R3) Ω 2 (k + 1)}
    (hU : ⇑(Wkp.iteratedGradient k U) =ᵐ[(volume : Measure R3).restrict Ω]
      topField k fun i => Wkp.lowerOrder k (g i)) :
    HasWeakFDerivOn volume Ω (Wkp.iteratedGradient k U)
      ((∑ i, (lift i k).compLp (Wkp.iteratedGradient k (g i)) :
        Lp (IteratedGradient R3 (k + 1)) 2 ((volume : Measure R3).restrict Ω))) := by
  refine ((hasWeakFDerivOn_topField k g).congr_ae hU.symm).congr_ae_deriv ?_
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (lift i k).compLp (Wkp.iteratedGradient k (g i))),
    ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp (lift i k)
      (Wkp.iteratedGradient k (g i))] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun i _ => (h2 i).symm

/-- Reconstruct `U ∈ W^{k+1,2}` from `w ∈ W^{1,2}` and `gᵢ ∈ W^{k,2}` with `gᵢ = ∂ᵢ w`. -/
def ofPartialsPack : (k : ℕ) → (w : W1p (volume : Measure R3) Ω 2) →
    (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 k) →
    (∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient w x i) →
    {U : Wkp (volume : Measure R3) Ω 2 (k + 1) // Wkp.firstOrder k U = w ∧
      ⇑(Wkp.iteratedGradient k U) =ᵐ[(volume : Measure R3).restrict Ω] topField k g}
  | 0, w, g, h => ⟨(w : Wkp (volume : Measure R3) Ω 2 1), rfl, by
      change ⇑(W1p.gradient w) =ᵐ[_] _
      filter_upwards [ae_all_iff.mpr h] with x hx
      simp only [topField, hx]
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (W1p.gradient w x)]
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]⟩
  | k + 1, w, g, h =>
    let U' := ofPartialsPack k w (fun i => Wkp.lowerOrder k (g i)) h
    ⟨Wkp.mk k U'.1 (∑ i, (lift i k).compLp (Wkp.iteratedGradient k (g i)))
      (ofPartials_hasWeakFDerivOn k g U'.2.2),
      by
        rw [Wkp.firstOrder_succ, Wkp.lowerOrder_mk]
        exact U'.2.1,
      by
        rw [Wkp.iteratedGradient_mk]
        filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
            (fun i => (lift i k).compLp (Wkp.iteratedGradient k (g i))),
          ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp (lift i k)
            (Wkp.iteratedGradient k (g i))] with x h1 h2
        rw [h1]
        exact Finset.sum_congr rfl fun i _ => h2 i⟩


/-- The function reconstructed from `w` and its partial derivatives `g`. -/
def ofPartials (k : ℕ) (w : W1p (volume : Measure R3) Ω 2)
    (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient w x i) : Wkp (volume : Measure R3) Ω 2 (k + 1) :=
  (ofPartialsPack k w g h).1

theorem firstOrder_ofPartials (k : ℕ) (w : W1p (volume : Measure R3) Ω 2)
    (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient w x i) :
    Wkp.firstOrder k (ofPartials k w g h) = w :=
  (ofPartialsPack k w g h).2.1

theorem value_ofPartials (k : ℕ) (w : W1p (volume : Measure R3) Ω 2)
    (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient w x i) :
    Wkp.value (k + 1) (ofPartials k w g h) = W1p.value w := by
  rw [← Wkp.value_firstOrder, firstOrder_ofPartials]

theorem norm_ofPartials_le : ∀ (k : ℕ) (w : W1p (volume : Measure R3) Ω 2)
    (g : Fin 3 → Wkp (volume : Measure R3) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient w x i),
    ‖ofPartials k w g h‖ ≤ ‖w‖ + k * ∑ i, ‖g i‖
  | 0, w, g, h => by simp only [CharP.cast_eq_zero, zero_mul, add_zero]; exact le_rfl
  | k + 1, w, g, h => by
      have hU' := norm_ofPartials_le k w (fun i => Wkp.lowerOrder k (g i)) h
      set U' := ofPartials k w (fun i => Wkp.lowerOrder k (g i)) h
      set F := ∑ i, (lift i k).compLp (Wkp.iteratedGradient k (g i))
      have hF : ‖F‖ ≤ ∑ i, ‖g i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (ContinuousLinearMap.norm_compLp_le _ _).trans ?_
        calc ‖lift i k‖ * ‖Wkp.iteratedGradient k (g i)‖ ≤ 1 * ‖g i‖ :=
              mul_le_mul (norm_lift_le i k) (Wkp.norm_iteratedGradient_le k (g i))
                (norm_nonneg _) zero_le_one
          _ = ‖g i‖ := one_mul _
      have hlow : ∑ i, ‖Wkp.lowerOrder k (g i)‖ ≤ ∑ i, ‖g i‖ :=
        Finset.sum_le_sum fun i _ => Wkp.norm_lowerOrder_le k (g i)
      have hsq := Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq (k + 1)
        (ofPartials (k + 1) w g h)
      have hlo : Wkp.lowerOrder (k + 1) (ofPartials (k + 1) w g h) = U' := by
        rw [ofPartials, ofPartialsPack]
        exact Wkp.lowerOrder_mk _ _ _ (ofPartials_hasWeakFDerivOn k g (ofPartialsPack k w _ h).2.2)
      have hig : Wkp.iteratedGradient (k + 1) (ofPartials (k + 1) w g h) = F := by
        rw [ofPartials, ofPartialsPack]
        exact Wkp.iteratedGradient_mk _ _ _
          (ofPartials_hasWeakFDerivOn k g (ofPartialsPack k w _ h).2.2)
      rw [hlo, hig] at hsq
      have hsum : 0 ≤ ∑ i, ‖g i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
      have hb : ‖ofPartials (k + 1) w g h‖ ≤ ‖U'‖ + ‖F‖ := by
        nlinarith [norm_nonneg (ofPartials (k + 1) w g h), norm_nonneg U', norm_nonneg F]
      push_cast
      nlinarith [norm_nonneg w, Nat.cast_nonneg (α := ℝ) k]

end OAI.AnisotropicCalderon.WkpCalculus
