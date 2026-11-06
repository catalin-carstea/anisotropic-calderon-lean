import Calderon.LocalPolynomialCoefficientL2Bound
import Calderon.ActualInterpolationExponent45
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory intervalIntegral Nat
open scoped Interval

/-- The degree-44 Taylor remainder is controlled by the genuine 45th Fréchet jet
on the segment. This is the analytic remainder needed by Section 06. -/
theorem norm_sub_taylor44_le (F : R3 → ℝ) (y h : R3) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hF : ∀ t : ℝ, t ∈ Icc 0 1 → ContDiffAt ℝ 45 F (y + t • h))
    (hM : ∀ t : ℝ, t ∈ Icc 0 1 → ‖iteratedFDeriv ℝ 45 F (y + t • h)‖ ≤ M) :
    ‖F (y + h) - (∑ k ∈ Finset.range 45,
      (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k F y (fun _ => h)))‖ ≤ M * ‖h‖ ^ 45 := by
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := 44) (f := F) (x := y) (y := h) hF
  rw [htaylor, add_sub_cancel_left]
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(1 - t)^44 • iteratedFDeriv ℝ 45 F (y + t • h) (fun _ => h)‖ ≤
        M * ‖h‖^45 := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr htI.2
    have ht1 : 1 - t ≤ 1 := by linarith [htI.1]
    have hpow : |1 - t|^44 ≤ 1 := pow_le_one₀ (abs_nonneg _) (by simpa [abs_of_nonneg ht0] using ht1)
    calc
      ‖(1 - t)^44 • iteratedFDeriv ℝ 45 F (y + t • h) (fun _ => h)‖
          = |1 - t|^44 * ‖iteratedFDeriv ℝ 45 F (y + t • h) (fun _ => h)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ |1 - t|^44 * (M * ‖h‖^45) := by
            gcongr
            exact (ContinuousMultilinearMap.le_opNorm_mul_pow_of_le
              (iteratedFDeriv ℝ 45 F (y + t • h)) (by simp)).trans
                (mul_le_mul_of_nonneg_right (hM t htI) (pow_nonneg (norm_nonneg _) _))
      _ ≤ M * ‖h‖^45 := by nlinarith [mul_nonneg hM0 (pow_nonneg (norm_nonneg h) 45)]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hint' : ‖∫ t in (0 : ℝ)..1,
      (1 - t)^44 • iteratedFDeriv ℝ 45 F (y + t • h) (fun _ => h)‖ ≤
      M * ‖h‖^45 := by simpa using hint
  rw [norm_smul]
  have hfac : |((44 ! : ℝ)⁻¹)| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact inv_le_one_of_one_le₀ (by norm_num : (1 : ℝ) ≤ 44 !)
  calc
    |((44 ! : ℝ)⁻¹)| * ‖∫ t in (0 : ℝ)..1,
        (1 - t)^44 • iteratedFDeriv ℝ 45 F (y + t • h) (fun _ => h)‖
      ≤ 1 * (M * ‖h‖^45) := mul_le_mul hfac hint' (norm_nonneg _) (by positivity)
    _ = M * ‖h‖^45 := one_mul _

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation



namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat

private theorem interpolation_scale_pow (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (r ^ ((1 : ℝ) / 23)) ^ n = r ^ ((n : ℝ) / 23) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1
  ring

private theorem interpolation_scale_remainder_power (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (r ^ ((1 : ℝ) / 23)) ^ j *
        r ^ (((45 : ℝ) - (j : ℝ)) / 23) =
      (r ^ ((1 : ℝ) / 23)) ^ 45 := by
  rw [interpolation_scale_pow r hr j, interpolation_scale_pow r hr 45,
    ← Real.rpow_add hr]
  congr 1
  ring

private theorem interpolation_scale_L2_power (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (r ^ ((1 : ℝ) / 23)) ^ j *
        r ^ ((2 : ℝ) - ((j : ℝ) + 3/2)/23) =
      (((r ^ ((1 : ℝ) / 23)) ^ 3)⁻¹) ^ ((1 : ℝ)/2) * r^2 := by
  have hhalf : (((r ^ ((3 : ℝ)/23))⁻¹) ^ ((1 : ℝ)/2)) =
      r ^ (-(3 : ℝ)/46) := by
    rw [← Real.rpow_neg hr.le, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [interpolation_scale_pow r hr j, interpolation_scale_pow r hr 3]
  simp only [Nat.cast_ofNat]
  rw [hhalf, ← Real.rpow_natCast, ← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 1
  ring

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation



namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat Filter
open scoped ContDiff Topology

private def wordJet (F : R3 → ℝ) (w : List R3) (x : R3) : ℝ :=
  iteratedFDeriv ℝ w.length F x w.get

/-- Adding a vector to a coordinate word differentiates the existing word
jet in that direction. -/
private theorem wordJet_cons_of_contDiffAt (F : R3 → ℝ)
    (w : List R3) (v x : R3) (hF : ContDiffAt ℝ ∞ F x) :
    wordJet F (v :: w) x = fderiv ℝ (wordJet F w) x v := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length F) x :=
    hF.differentiableAt_iteratedFDeriv (by
      exact_mod_cast (ENat.natCast_lt_top w.length))
  have htail : Fin.tail (v :: w).get = w.get := by
    funext i
    simp [Fin.tail, List.get]
  have h := DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := F) (n := w.length) (x := x)
    (m := (v :: w).get) hd
  unfold wordJet
  simpa [htail] using h

/-- Every fixed word jet is twice differentiable under local smoothness. -/
private theorem contDiffAt_wordJet_two (F : R3 → ℝ)
    (w : List R3) (x : R3) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ 2 (wordJet F w) x := by
  have hD : ContDiffAt ℝ 2 (iteratedFDeriv ℝ w.length F) x :=
    hF.iteratedFDeriv_right (by
      change (((2 : ℕ∞) + (w.length : ℕ∞) : ℕ∞) : ℕ∞ω) ≤
        ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  let ev : (R3 [×w.length]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.length => R3) ℝ w.get
  have hev : ContDiffAt ℝ 2 ev (iteratedFDeriv ℝ w.length F x) :=
    ev.contDiff.contDiffAt
  change ContDiffAt ℝ 2
    (fun z => (iteratedFDeriv ℝ w.length F z) w.get) x
  simpa [ev, Function.comp_def] using hev.comp x hD

private theorem fderiv_fderiv_apply_const (g : R3 → ℝ)
    (x a b : R3) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fun z => fderiv ℝ g z b) x a =
      fderiv ℝ (fderiv ℝ g) x a b := by
  have hfg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := congrArg (fun T : R3 →L[ℝ] ℝ => T a)
    (fderiv_clm_apply hfg (differentiableAt_const b))
  simpa using h

/-- The adjacent leading vectors of a fixed word commute by finite Schwarz
symmetry; local C-infinity is available for the source fields. -/
private theorem wordJet_swap_of_contDiffOn (F : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (w : List R3) (a b x : R3) (hx : x ∈ U) :
    wordJet F (a :: b :: w) x = wordJet F (b :: a :: w) x := by
  let g : R3 → ℝ := wordJet F w
  have hFx : ContDiffAt ℝ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have hg : ContDiffAt ℝ 2 g x := contDiffAt_wordJet_two F w x hFx
  have hbevent : wordJet F (b :: w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ g z b) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact wordJet_cons_of_contDiffAt F w b z (hF.contDiffAt (hU.mem_nhds hz))
  have haevent : wordJet F (a :: w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ g z a) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact wordJet_cons_of_contDiffAt F w a z (hF.contDiffAt (hU.mem_nhds hz))
  have hsym := (hg.isSymmSndFDerivAt (by norm_num)).eq a b
  calc
    wordJet F (a :: b :: w) x =
      fderiv ℝ (wordJet F (b :: w)) x a :=
        wordJet_cons_of_contDiffAt F (b :: w) a x hFx
    _ = fderiv ℝ (fun z => fderiv ℝ g z b) x a := by
      rw [hbevent.fderiv_eq]
    _ = fderiv ℝ (fderiv ℝ g) x a b :=
      fderiv_fderiv_apply_const g x a b hg
    _ = fderiv ℝ (fderiv ℝ g) x b a := hsym
    _ = fderiv ℝ (fun z => fderiv ℝ g z a) x b :=
      (fderiv_fderiv_apply_const g x b a hg).symm
    _ = fderiv ℝ (wordJet F (a :: w)) x b := by
      rw [haevent.fderiv_eq]
    _ = wordJet F (b :: a :: w) x :=
      (wordJet_cons_of_contDiffAt F (a :: w) b x hFx).symm

/-- Finite Schwarz symmetry for a list of directional Fréchet evaluations on
an open smoothness domain. List permutation induction propagates the local
two-vector swap through every derivative position. -/
private theorem wordJet_perm_of_contDiffOn (F : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {w₁ w₂ : List R3} (hp : w₁.Perm w₂) :
    ∀ x ∈ U, wordJet F w₁ x = wordJet F w₂ x := by
  induction hp with
  | nil =>
      intro x hx
      rfl
  | @cons a w₁ w₂ hp ih =>
      intro x hx
      have hFx : ContDiffAt ℝ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
      have hevent : wordJet F w₁ =ᶠ[𝓝 x] wordJet F w₂ := by
        filter_upwards [hU.mem_nhds hx] with z hz
        exact ih z hz
      calc
        wordJet F (a :: w₁) x =
          fderiv ℝ (wordJet F w₁) x a :=
            wordJet_cons_of_contDiffAt F w₁ a x hFx
        _ = fderiv ℝ (wordJet F w₂) x a := by
          rw [hevent.fderiv_eq]
        _ = wordJet F (a :: w₂) x :=
          (wordJet_cons_of_contDiffAt F w₂ a x hFx).symm
  | @swap a b w =>
      intro x hx
      exact wordJet_swap_of_contDiffOn F U hU hF w b a x hx
  | @trans w₁ w₂ w₃ hp₁ hp₂ ih₁ ih₂ =>
      intro x hx
      exact (ih₁ x hx).trans (ih₂ x hx)

private theorem wordJet_ofFn (F : R3 → ℝ) (y : R3)
    (k : ℕ) (v : Fin k → R3) :
    wordJet F (List.ofFn v) y = iteratedFDeriv ℝ k F y v := by
  have hpair : (⟨(List.ofFn v).length, (List.ofFn v).get⟩ :
      Σ n : ℕ, Fin n → R3) = ⟨k, v⟩ :=
    List.equivSigmaTuple.apply_symm_apply ⟨k, v⟩
  exact congrArg
    (fun p : Σ n : ℕ, Fin n → R3 =>
      iteratedFDeriv ℝ p.1 F y p.2) hpair

/-- Finite-order Schwarz symmetry of genuine iterated Fréchet derivatives on
an open smoothness domain. -/
theorem iteratedFDeriv_comp_perm_of_contDiffOn_open (F : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (y : R3) (hy : y ∈ U) (k : ℕ)
    (v : Fin k → R3) (σ : Equiv.Perm (Fin k)) :
    iteratedFDeriv ℝ k F y (v ∘ σ) =
      iteratedFDeriv ℝ k F y v := by
  have h := wordJet_perm_of_contDiffOn F U hU hF
    (σ.ofFn_comp_perm v) y hy
  simpa only [wordJet_ofFn] using h

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Local finite smoothness on the physical closed ball implies L² membership
of its affine pullback on the unit ball. -/
theorem memLp_affine_unitBall_of_contDiffAt_closedBall
    (F : R3 → ℝ) (y : R3) (s : ℝ) (hs : 0 < s)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ 45 F x) :
    MemLp (fun z : R3 => F (y + s • z)) 2
      (volume.restrict (ball (0 : R3) 1)) := by
  let G : R3 → ℝ := fun z => F (y + s • z)
  let K : Set R3 := closedBall (0 : R3) 1
  let μ : Measure R3 := volume.restrict (ball (0 : R3) 1)
  have hmap (z : R3) (hz : z ∈ K) : y + s • z ∈ closedBall y s := by
    have hz' : ‖z‖ ≤ 1 := by
      simpa [K, mem_closedBall, dist_eq_norm] using hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hz')]
  have hGcont : ContinuousOn G K := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hAff : ContinuousAt (fun w : R3 => y + s • w) z := by fun_prop
    exact ContinuousAt.comp' (hF _ (hmap z hz)).continuousAt hAff
  have hKcompact : IsCompact K := isCompact_closedBall (0 : R3) 1
  have hGmeas : AEStronglyMeasurable G μ :=
    hGcont.aestronglyMeasurable_of_subset_isCompact hKcompact measurableSet_ball
      (by exact ball_subset_closedBall)
  obtain ⟨C,hC⟩ := hKcompact.exists_bound_of_continuousOn hGcont
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply MemLp.of_bound hGmeas C
  filter_upwards [ae_restrict_mem (measurableSet_ball :
    MeasurableSet (ball (0 : R3) 1))] with z hz
  exact hC z (ball_subset_closedBall hz)

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation



namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat

/-- Expansion of a genuine continuous multilinear jet in the three standard
coordinate directions. The sum is over words, before collecting monomials. -/
theorem diagonal_jet_eq_sum_coordinate_words (k : ℕ)
    (T : R3 [×k]→L[ℝ] ℝ) (z : R3) :
    T (fun _ : Fin k => z) =
      ∑ w : Fin k → Fin 3,
        (∏ j : Fin k, z (w j)) *
          T (fun j : Fin k => EuclideanSpace.basisFun (Fin 3) ℝ (w j)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hz : z = ∑ i : Fin 3, z i • b i := by
    simpa [b] using (b.sum_repr z).symm
  calc
    T (fun _ : Fin k => z) =
        T (fun _ : Fin k => ∑ i : Fin 3, z i • b i) := by rw [← hz]
    _ = ∑ w : Fin k → Fin 3,
          T (fun j : Fin k => z (w j) • b (w j)) := by
            exact T.toMultilinearMap.map_sum (fun (_j : Fin k) (i : Fin 3) => z i • b i)
    _ = ∑ w : Fin k → Fin 3,
          (∏ j : Fin k, z (w j)) * T (fun j : Fin k => b (w j)) := by
            apply Finset.sum_congr rfl
            intro w _
            exact (T.toMultilinearMap.map_smul_univ (fun j : Fin k => z (w j))
                (fun j : Fin k => b (w j)))
    _ = _ := rfl

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat MvPolynomial

/-- The diagonal of every genuine Fréchet multilinear jet has a concrete
three-variable polynomial representative, with a word-indexed expansion. -/
theorem exists_diagonal_jet_mvPolynomial (k : ℕ)
    (T : R3 [×k]→L[ℝ] ℝ) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p.totalDegree ≤ k ∧
      ∀ z : R3, MvPolynomial.eval (fun i : Fin 3 => z i) p =
        T (fun _ : Fin k => z) := by
  classical
  let p : MvPolynomial (Fin 3) ℝ :=
    ∑ w : Fin k → Fin 3,
      MvPolynomial.C (T (fun j : Fin k => EuclideanSpace.basisFun (Fin 3) ℝ (w j))) *
        ∏ j : Fin k, MvPolynomial.X (w j)
  refine ⟨p, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro w _
    calc
      (MvPolynomial.C (T (fun j : Fin k => EuclideanSpace.basisFun (Fin 3) ℝ (w j))) *
          ∏ j : Fin k, MvPolynomial.X (w j)).totalDegree
          ≤ (MvPolynomial.C (T (fun j : Fin k => EuclideanSpace.basisFun (Fin 3) ℝ (w j)))).totalDegree +
              (∏ j : Fin k, MvPolynomial.X (w j)).totalDegree :=
                MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + ∑ j : Fin k, (MvPolynomial.X (w j) : MvPolynomial (Fin 3) ℝ).totalDegree := by
            simp only [MvPolynomial.totalDegree_C, zero_add]
            exact MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin k))
              (fun j => (MvPolynomial.X (w j) : MvPolynomial (Fin 3) ℝ))
      _ = k := by simp
  intro z
  have hw := diagonal_jet_eq_sum_coordinate_words k T z
  rw [hw]
  simp only [p, map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro w _
  ring

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat MvPolynomial

/-- The actual order-44 Fréchet Taylor sum on the scale `s` is a concrete
polynomial of total degree at most 44 in the unit-ball coordinates. -/
theorem exists_taylor44_mvPolynomial (F : R3 → ℝ) (y : R3) (s : ℝ) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p.totalDegree ≤ 44 ∧
      ∀ z : R3, MvPolynomial.eval (fun i : Fin 3 => z i) p =
        ∑ k ∈ Finset.range 45, (k ! : ℝ)⁻¹ •
          (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)) := by
  classical
  let T (k : ℕ) : R3 [×k]→L[ℝ] ℝ := iteratedFDeriv ℝ k F y
  have hq (k : ℕ) : ∃ p : MvPolynomial (Fin 3) ℝ,
      p.totalDegree ≤ k ∧
      ∀ z : R3, MvPolynomial.eval (fun i : Fin 3 => z i) p =
        T k (fun _ : Fin k => z) := exists_diagonal_jet_mvPolynomial k (T k)
  let q (k : ℕ) : MvPolynomial (Fin 3) ℝ := Classical.choose (hq k)
  have hqdeg (k : ℕ) : (q k).totalDegree ≤ k := (Classical.choose_spec (hq k)).1
  have hqeval (k : ℕ) (z : R3) :
      MvPolynomial.eval (fun i : Fin 3 => z i) (q k) = T k (fun _ : Fin k => z) :=
        (Classical.choose_spec (hq k)).2 z
  let p : MvPolynomial (Fin 3) ℝ :=
    ∑ k ∈ Finset.range 45, MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k) * q k
  refine ⟨p, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    have hk44 : k ≤ 44 := by
      simp only [Finset.mem_range] at hk
      omega
    calc
      (MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k) * q k).totalDegree
          ≤ (MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k)).totalDegree + (q k).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = (q k).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ k := hqdeg k
      _ ≤ 44 := hk44
  intro z
  have hs (k : ℕ) :
      T k (fun _ : Fin k => s • z) = s^k * T k (fun _ : Fin k => z) := by
    have h := (T k).toMultilinearMap.map_smul_univ (fun _ : Fin k => s)
      (fun _ : Fin k => z)
    change T k (fun _ : Fin k => s • z) = (∏ _j : Fin k, s) * T k (fun _ : Fin k => z) at h
    simpa only [Finset.prod_const, Finset.card_fin, nsmul_eq_mul] using h
  simp only [p, map_sum, map_mul, MvPolynomial.eval_C, hqeval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hs]
  simp only [smul_eq_mul]
  ring

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat MvPolynomial

/-- Any polynomial of total degree at most `m` uses exactly the finite
coordinate multi-index family of the checked L² coefficient theorem. -/
theorem exists_bounded_degree_coefficient_expansion (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.totalDegree ≤ m) :
    let I := {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
    ∃ a : I → ℝ, ∀ z : R3,
      MvPolynomial.eval (fun i : Fin 3 => z i) p =
        ∑ beta : I, a beta * ∏ i : Fin 3, (z i) ^ (beta.val i).val := by
  classical
  let I := {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
  let e : I → (Fin 3 →₀ ℕ) := fun beta =>
    Finsupp.equivFunOnFinite.symm (fun i => (beta.val i).val)
  have he : Function.Injective e := by
    intro alpha beta h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hi := congrArg (fun d : Fin 3 →₀ ℕ => d i) h
    simpa only [e, Finsupp.coe_equivFunOnFinite_symm] using hi
  have hsurj (d : Fin 3 →₀ ℕ) (hd : d ∈ p.support) : ∃ beta : I, e beta = d := by
    have hdi (i : Fin 3) : d i ≤ m :=
      ((MvPolynomial.le_degreeOf_of_mem_support i hd).trans
        (MvPolynomial.degreeOf_le_totalDegree p i)).trans hp
    let beta : I := ⟨fun i => ⟨d i, Nat.lt_succ_of_le (hdi i)⟩, by
      simpa only [Finsupp.sum_fintype (f := d) (g := fun _ e => e) (by simp)] using
        (MvPolynomial.le_totalDegree hd).trans hp⟩
    refine ⟨beta, ?_⟩
    ext i
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  let a : I → ℝ := fun beta => p.coeff (e beta)
  let q : MvPolynomial (Fin 3) ℝ := ∑ beta : I, MvPolynomial.monomial (e beta) (a beta)
  have hpq : p = q := by
    ext d
    by_cases hd : d ∈ p.support
    · obtain ⟨beta, hbeta⟩ := hsurj d hd
      subst d
      simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      have hsum : (∑ gamma : I, if e gamma = e beta then a gamma else 0) = a beta := by
        simp only [he.eq_iff]
        exact Fintype.sum_ite_eq' beta a
      simpa only [a] using hsum.symm
    · have hzero : p.coeff d = 0 := by simpa only [MvPolynomial.mem_support_iff, not_ne_iff] using hd
      simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      rw [hzero]
      symm
      apply Finset.sum_eq_zero
      intro beta _
      by_cases h : e beta = d
      · simp only [h, ↓reduceIte, a, hzero]
      · simp [h]

  refine ⟨a, ?_⟩
  intro z
  rw [hpq]
  simp only [q, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro beta _
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat MvPolynomial
open scoped ENNReal

/-- The actual scaled Taylor sum has coefficients controlled by its unit-ball
L² norm, using the already checked finite-dimensional coefficient theorem. -/
theorem exists_taylor44_coefficients_with_L2_bound :
    let I := {alpha : Fin 3 → Fin 45 // ∑ i, (alpha i).val ≤ 44}
    ∃ C : ℝ, 0 < C ∧ ∀ (F : R3 → ℝ) (y : R3) (s : ℝ),
      ∃ a : I → ℝ,
        (∀ z : R3,
          (∑ k ∈ Finset.range 45, (k ! : ℝ)⁻¹ •
            (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z))) =
          ∑ beta : I, a beta * ∏ i : Fin 3, (z i) ^ (beta.val i).val) ∧
        (∀ alpha : I,
          |a alpha| ≤ C *
            (eLpNorm
              (fun z : R3 => ∑ k ∈ Finset.range 45, (k ! : ℝ)⁻¹ •
                (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)))
              2 (volume.restrict (ball (0 : R3) 1))).toReal) := by
  classical
  let I := {alpha : Fin 3 → Fin 45 // ∑ i, (alpha i).val ≤ 44}
  obtain ⟨C,hCpos,hC⟩ := exists_polynomial_coefficient_le_unitBall_eLpNorm 44
  refine ⟨C,hCpos,?_⟩
  intro F y s
  obtain ⟨p,hdeg,hpeval⟩ := exists_taylor44_mvPolynomial F y s
  obtain ⟨a,ha⟩ := exists_bounded_degree_coefficient_expansion 44 p hdeg
  refine ⟨a,?_,?_⟩
  · intro z
    exact (hpeval z).symm.trans (ha z)
  intro alpha
  have h := hC a alpha
  simpa only [← ha, ← hpeval] using h

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat

/-- The actual Taylor remainder on the scaled unit ball, with the 45th
Fréchet norm bounded on the physical closed ball. -/
theorem norm_sub_taylor44_on_unitBall_le (F : R3 → ℝ) (y : R3) (s M : ℝ)
    (hs : 0 < s) (hM0 : 0 ≤ M)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ 45 F x)
    (hM : ∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ 45 F x‖ ≤ M)
    (z : R3) (hz : z ∈ ball (0 : R3) 1) :
    ‖F (y + s • z) - (∑ k ∈ Finset.range 45,
      (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)))‖ ≤
        M * s^45 := by
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) : y + t • (s • z) ∈ closedBall y s := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht0 : 0 ≤ t := ht.1
    have hts : 0 ≤ t * s := mul_nonneg ht0 hs.le
    have htsle : t * s ≤ s := by nlinarith [ht.2]
    rw [abs_of_nonneg ht0, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le]
    calc
      t * (s * ‖z‖) = (t * s) * ‖z‖ := by ring
      _ ≤ (t * s) * 1 := mul_le_mul_of_nonneg_left hz1 hts
      _ ≤ s := by simpa using htsle
  have hbase := norm_sub_taylor44_le F y (s • z) M hM0
    (fun t ht => hF _ (hseg t ht)) (fun t ht => hM _ (hseg t ht))
  have hnorm : ‖s • z‖ ≤ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hz1)]
  exact hbase.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 45) hM0)

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ContDiff

private def coordinateMonomial {m : ℕ}
    (beta : {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m})
    (z : R3) : ℝ := ∏ i : Fin 3, (z i) ^ (beta.val i).val

private theorem contDiff_coordinateMonomial {m : ℕ}
    (beta : {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}) :
    ContDiff ℝ ∞ (coordinateMonomial beta) := by
  unfold coordinateMonomial
  fun_prop

/-- Every derivative of a finite coordinate polynomial is bounded by the
corresponding coefficient-weighted sum of its genuine monomial derivatives. -/
theorem norm_iteratedFDeriv_coordinate_polynomial_le (m j : ℕ)
    (a : {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m} → ℝ) :
    ‖iteratedFDeriv ℝ j
      (fun z : R3 => ∑ beta, a beta * ∏ i : Fin 3, (z i) ^ (beta.val i).val)
      (0 : R3)‖ ≤
    ∑ beta, |a beta| * ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖ := by
  classical
  let I := {alpha : Fin 3 → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
  let g : I → R3 → ℝ := fun beta z => a beta * coordinateMonomial beta z
  have hg (beta : I) : ContDiffAt ℝ j (g beta) (0 : R3) := by
    exact ((contDiff_const.mul (contDiff_coordinateMonomial beta)).of_le (by simp)).contDiffAt
  have hsum := iteratedFDeriv_fun_sum_apply (u := Finset.univ) (x := (0 : R3))
    (fun beta _ => hg beta)
  change iteratedFDeriv ℝ j (fun z : R3 => ∑ beta : I, g beta z) (0 : R3) =
    ∑ beta : I, iteratedFDeriv ℝ j (g beta) (0 : R3) at hsum
  change ‖iteratedFDeriv ℝ j (fun z : R3 => ∑ beta : I, g beta z) (0 : R3)‖ ≤
    ∑ beta : I, |a beta| * ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖
  rw [hsum]
  calc
    ‖∑ beta : I, iteratedFDeriv ℝ j (g beta) (0 : R3)‖
        ≤ ∑ beta : I, ‖iteratedFDeriv ℝ j (g beta) (0 : R3)‖ := norm_sum_le _ _
    _ = ∑ beta : I, |a beta| * ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖ := by
      apply Finset.sum_congr rfl
      intro beta _
      have hb := iteratedFDeriv_const_smul_apply'
        (i := j) (x := (0 : R3)) (a := a beta) (f := coordinateMonomial beta)
        ((contDiff_coordinateMonomial beta).of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt
      simpa only [g, smul_eq_mul, norm_smul, Real.norm_eq_abs] using congrArg norm hb

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

private def taylor44 (F : R3 → ℝ) (y : R3) (s : ℝ) (z : R3) : ℝ :=
  ∑ k ∈ Finset.range 45, (k ! : ℝ)⁻¹ •
    (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z))

/-- The checked coefficient L² theorem controls each order-0-through-10
Fréchet derivative of the actual finite Taylor polynomial at the origin.
The constant is uniform in the function, center and scale. -/
theorem exists_uniform_taylor44_polynomial_deriv_le_unitBall_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : R3 → ℝ) (y : R3) (s : ℝ)
      (j : ℕ), j ≤ 10 →
      ‖iteratedFDeriv ℝ j (taylor44 F y s) (0 : R3)‖ ≤
        C * (eLpNorm (taylor44 F y s) 2
          (volume.restrict (ball (0 : R3) 1))).toReal := by
  classical
  let I := {alpha : Fin 3 → Fin 45 // ∑ i, (alpha i).val ≤ 44}
  obtain ⟨Cp,hCp,hCoeff⟩ := exists_taylor44_coefficients_with_L2_bound
  let B : ℝ := ∑ j ∈ Finset.range 11,
    ∑ beta : I, ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Cp * (B + 1), mul_pos hCp (by linarith), ?_⟩
  intro F y s j hj
  obtain ⟨a,ha,hca⟩ := hCoeff F y s
  have hfun : taylor44 F y s =
      fun z : R3 => ∑ beta : I, a beta * coordinateMonomial beta z := by
    funext z
    simpa only [taylor44, coordinateMonomial] using ha z
  have hB : (∑ beta : I,
      ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖) ≤ B := by
    change (∑ beta : I, ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖) ≤
      ∑ k ∈ Finset.range 11, ∑ beta : I, ‖iteratedFDeriv ℝ k (coordinateMonomial beta) (0 : R3)‖
    exact Finset.single_le_sum
      (s := Finset.range 11)
      (f := fun k => ∑ beta : I,
        ‖iteratedFDeriv ℝ k (coordinateMonomial beta) (0 : R3)‖)
      (a := j)
      (fun k hk => Finset.sum_nonneg (fun beta _ => norm_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hN0 : 0 ≤ (eLpNorm (taylor44 F y s) 2
      (volume.restrict (ball (0 : R3) 1))).toReal := ENNReal.toReal_nonneg
  calc
    ‖iteratedFDeriv ℝ j (taylor44 F y s) (0 : R3)‖
      = ‖iteratedFDeriv ℝ j
          (fun z : R3 => ∑ beta : I, a beta * coordinateMonomial beta z)
          (0 : R3)‖ := by rw [hfun]
    _
      ≤ ∑ beta : I, |a beta| *
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖ :=
            norm_iteratedFDeriv_coordinate_polynomial_le 44 j a
    _ ≤ ∑ beta : I,
        (Cp * (eLpNorm (taylor44 F y s) 2
          (volume.restrict (ball (0 : R3) 1))).toReal) *
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖ := by
            apply Finset.sum_le_sum
            intro beta _
            exact mul_le_mul_of_nonneg_right (hca beta) (norm_nonneg _)
    _ = (Cp * (eLpNorm (taylor44 F y s) 2
          (volume.restrict (ball (0 : R3) 1))).toReal) *
        (∑ beta : I,
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : R3)‖) := by
            rw [Finset.mul_sum]
    _ ≤ (Cp * (eLpNorm (taylor44 F y s) 2
          (volume.restrict (ball (0 : R3) 1))).toReal) * B := by
            exact mul_le_mul_of_nonneg_left hB (mul_nonneg hCp.le hN0)
    _ ≤ (Cp * (B + 1)) *
        (eLpNorm (taylor44 F y s) 2
          (volume.restrict (ball (0 : R3) 1))).toReal := by
            nlinarith [mul_nonneg hCp.le hN0]

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

/-- The derivative of the actual finite Taylor sum recovers the scaled source
jet. The explicit symmetry premise isolates the finite-order Schwarz step. -/
theorem iteratedFDeriv_taylor44_at_zero_of_symmetric (F : R3 → ℝ)
    (y : R3) (s : ℝ) (j : ℕ) (hj : j ≤ 44)
    (hSym : ∀ k : ℕ, k ≤ 44 → ∀ (v : Fin k → R3) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℝ k F y (v ∘ σ) = iteratedFDeriv ℝ k F y v) :
    iteratedFDeriv ℝ j (taylor44 F y s) (0 : R3) =
      s^j • iteratedFDeriv ℝ j F y := by
  classical
  let p : FormalMultilinearSeries ℝ R3 ℝ := fun k =>
    if k < 45 then ((k ! : ℝ)⁻¹ * s^k) • iteratedFDeriv ℝ k F y else 0
  have hfinite (k : ℕ) (hk : 45 ≤ k) : p k = 0 := by simp [p, Nat.not_lt.mpr hk]
  have hsum (z : R3) :
      (∑ k ∈ Finset.range 45, p k (fun _ : Fin k => z)) = taylor44 F y s z := by
    simp only [p, Finset.sum_apply, Finset.mem_range, dite_true, taylor44]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < 45 := Finset.mem_range.mp hk
    rw [if_pos hk']
    have hscale := (iteratedFDeriv ℝ k F y).toMultilinearMap.map_smul_univ
      (fun _ : Fin k => s) (fun _ : Fin k => z)
    change iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z) =
      (∏ _i : Fin k, s) * iteratedFDeriv ℝ k F y (fun _ : Fin k => z) at hscale
    rw [hscale]
    simp only [Finset.prod_const, Finset.card_fin, smul_apply, smul_eq_mul]
    ring
  have hseries : HasFiniteFPowerSeriesOnBall (taylor44 F y s) p
      (0 : R3) 45 ∞ := by
    apply HasFiniteFPowerSeriesOnBall.mk' hfinite (by simp)
    intro z hz
    simpa only [zero_add] using (hsum z)
  have hjlt : j < 45 := by omega
  have hderiv (v : Fin j → R3) :=
    hseries.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace v
  ext v
  rw [hderiv]
  have hpj : p j = ((j ! : ℝ)⁻¹ * s^j) • iteratedFDeriv ℝ j F y := by
    simp [p, hjlt]
  simp only [hpj, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hsym (σ : Equiv.Perm (Fin j)) :
      iteratedFDeriv ℝ j F y (fun i => v (σ i)) = iteratedFDeriv ℝ j F y v :=
    hSym j hj v σ
  simp_rw [hsym]
  simp [Fintype.card_perm, mul_assoc, Nat.factorial_ne_zero]

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Exact three-dimensional Jacobian for the affine chart of the physical
interpolation ball. -/
theorem map_volume_restrict_unitBall_affine (y : R3) (s : ℝ) (hs : 0 < s) :
    Measure.map (fun z : R3 => y + s • z)
      (volume.restrict (ball (0 : R3) 1)) =
    ENNReal.ofReal ((s^3)⁻¹) •
      (volume.restrict (ball y s)) := by
  have hsmul : Measure.map (fun z : R3 => s • z) volume =
      ENNReal.ofReal ((s^3)⁻¹) • (volume : Measure R3) := by
    convert Measure.map_addHaar_smul (volume : Measure R3) hs.ne' using 1
    simp [finrank_euclideanSpace_fin, abs_of_pos (pow_pos hs 3)]
  have hmap : Measure.map (fun z : R3 => y + s • z) volume =
      ENNReal.ofReal ((s^3)⁻¹) • (volume : Measure R3) := by
    calc
      Measure.map (fun z : R3 => y + s • z) volume =
          Measure.map (fun x : R3 => x + y)
            (Measure.map (fun z : R3 => s • z) volume) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              congr 1
              funext z
              simp [Function.comp_def, add_comm]
      _ = ENNReal.ofReal ((s^3)⁻¹) • (volume : Measure R3) := by
            rw [hsmul, Measure.map_smul _ (by fun_prop)]
            simp only [map_add_right_eq_self]
  have hpre : (fun z : R3 => y + s • z) ⁻¹' ball y s = ball (0 : R3) 1 := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs, sub_zero]
    constructor
    · intro h
      by_contra hn
      have hn' : 1 ≤ ‖z‖ := le_of_not_gt hn
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hn')]
    · intro h
      nlinarith [mul_pos hs (sub_pos.mpr h)]
  have hmeasure := Measure.restrict_map
    (μ := (volume : Measure R3)) (f := fun z : R3 => y + s • z)
    (by fun_prop : Measurable fun z : R3 => y + s • z)
    (s := ball y s) isOpen_ball.measurableSet
  rw [hmap, hpre] at hmeasure
  simpa only [Measure.restrict_smul] using hmeasure.symm

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Exact L² change of variables from the physical radius-`s` ball to the
unit ball; the factor is the square root of the inverse 3D Jacobian. -/
theorem eLpNorm_affine_unitBall_eq_scaled_physicalBall
    (F : R3 → ℝ) (hF : Measurable F) (y : R3) (s : ℝ) (hs : 0 < s) :
    eLpNorm (fun z : R3 => F (y + s • z)) 2
        (volume.restrict (ball (0 : R3) 1)) =
      (ENNReal.ofReal ((s^3)⁻¹)) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm F 2 (volume.restrict (ball y s)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((s^3)⁻¹)
  have hc : c ≠ 0 := by
    have hs3 : 0 < s^3 := pow_pos hs _
    simp [c, hs3]
  have hmap := map_volume_restrict_unitBall_affine y s hs
  have htransport := eLpNorm_map_measure
    (p := (2 : ℝ≥0∞)) (f := fun z : R3 => y + s • z)
    (g := F) (μ := volume.restrict (ball (0 : R3) 1))
    (hF.aestronglyMeasurable)
    (by fun_prop : AEMeasurable (fun z : R3 => y + s • z)
      (volume.restrict (ball (0 : R3) 1)))
  rw [hmap] at htransport
  have hscalar := eLpNorm_smul_measure_of_ne_zero hc F
    (2 : ℝ≥0∞) (volume.restrict (ball y s))
  simpa only [c, smul_eq_mul, Function.comp_def] using htransport.symm.trans hscalar

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Real-valued form of the exact physical-ball L² scaling factor. -/
theorem eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall
    (F : R3 → ℝ) (hF : Measurable F) (y : R3) (s : ℝ) (hs : 0 < s) :
    (eLpNorm (fun z : R3 => F (y + s • z)) 2
        (volume.restrict (ball (0 : R3) 1))).toReal =
      ((s^3)⁻¹) ^ ((1 : ℝ) / 2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by
  rw [eLpNorm_affine_unitBall_eq_scaled_physicalBall F hF y s hs,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  have hs3 : 0 ≤ s^3 := (pow_pos hs 3).le
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hs3)]
  norm_num

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation


namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- A bounded pointwise Taylor remainder gives an actual L² bound for its
polynomial on the unit ball. -/
theorem lpNorm_taylor44_le_affine_lpNorm_add_remainder
    (F : R3 → ℝ) (y : R3) (s M : ℝ)
    (hs : 0 < s) (hM0 : 0 ≤ M)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ 45 F x)
    (hM : ∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ 45 F x‖ ≤ M)
    (hLp : MemLp (fun z : R3 => F (y + s • z)) 2
      (volume.restrict (ball (0 : R3) 1))) :
    (eLpNorm (taylor44 F y s) 2
      (volume.restrict (ball (0 : R3) 1))).toReal ≤
      (eLpNorm (fun z : R3 => F (y + s • z)) 2
        (volume.restrict (ball (0 : R3) 1))).toReal +
      M * s^45 *
        ((volume.restrict (ball (0 : R3) 1)).real .univ ^
          (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)) := by
  let μ : Measure R3 := volume.restrict (ball (0 : R3) 1)
  let G : R3 → ℝ := fun z => F (y + s • z)
  let P : R3 → ℝ := taylor44 F y s
  have hPcont : Continuous P := by
    obtain ⟨p, _, hp⟩ := exists_taylor44_mvPolynomial F y s
    have hPeq : P = fun z : R3 => MvPolynomial.eval (fun i : Fin 3 => z i) p := by
      funext z
      exact (hp z).symm
    rw [hPeq]
    exact (MvPolynomial.continuous_eval p).comp (by fun_prop)
  have hPmeas : AEStronglyMeasurable P μ := hPcont.measurable.aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (G - P) μ :=
    hLp.aestronglyMeasurable.sub hPmeas
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hRbound : ∀ᵐ z ∂μ, ‖(G - P) z‖ ≤ M * s^45 := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : R3) 1))]
      with z hz
    exact norm_sub_taylor44_on_unitBall_le F y s M hs hM0 hF hM z hz
  have hRlp : MemLp (G - P) 2 μ :=
    MemLp.of_bound hRmeas (M * s^45) hRbound
  have hRnorm : lpNorm (G - P) 2 μ ≤
      M * s^45 * (μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)) := by
    have hClp : MemLp (fun _ : R3 => M * s^45) 2 μ := memLp_const _
    calc
      lpNorm (G - P) 2 μ ≤ lpNorm (fun _ : R3 => M * s^45) 2 μ := by
        exact ENNReal.toReal_mono hClp.eLpNorm_ne_top
          (eLpNorm_mono_ae_real hRmeas hRbound)
      _ = _ := by
        rw [lpNorm_const' (by norm_num) (by norm_num)]
        simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM0 (pow_nonneg hs.le _))]
  have hPsub : P = G - (G - P) := by
    funext z
    simp [G, P]
  change lpNorm P 2 μ ≤ lpNorm G 2 μ +
    M * s^45 * (μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ))
  rw [hPsub]
  calc
    lpNorm (G - (G - P)) 2 μ ≤ lpNorm G 2 μ + lpNorm (G - P) 2 μ :=
      lpNorm_sub_le hLp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ _ := add_le_add_right hRnorm _

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- The affine L² change of variables only needs measurability on the
physical ball. -/
theorem eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall_local
    (F : R3 → ℝ) (y : R3) (s : ℝ) (hs : 0 < s)
    (hF : AEStronglyMeasurable F (volume.restrict (ball y s))) :
    (eLpNorm (fun z : R3 => F (y + s • z)) 2
        (volume.restrict (ball (0 : R3) 1))).toReal =
      ((s^3)⁻¹) ^ ((1 : ℝ) / 2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((s^3)⁻¹)
  have hc : c ≠ 0 := by
    have hs3 : 0 < s^3 := pow_pos hs _
    simp [c, hs3]
  have hmap := map_volume_restrict_unitBall_affine y s hs
  have hFmap : AEStronglyMeasurable F
      (Measure.map (fun z : R3 => y + s • z)
        (volume.restrict (ball (0 : R3) 1))) := by
    rw [hmap]
    exact hF.smul_measure c
  have htransport := eLpNorm_map_measure
    (p := (2 : ℝ≥0∞)) (f := fun z : R3 => y + s • z)
    (g := F) (μ := volume.restrict (ball (0 : R3) 1))
    hFmap
    (by fun_prop : AEMeasurable (fun z : R3 => y + s • z)
      (volume.restrict (ball (0 : R3) 1)))
  rw [hmap] at htransport
  have hscalar := eLpNorm_smul_measure_of_ne_zero hc F
    (2 : ℝ≥0∞) (volume.restrict (ball y s))
  have hnorm : eLpNorm (fun z : R3 => F (y + s • z)) 2
      (volume.restrict (ball (0 : R3) 1)) =
        c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          eLpNorm F 2 (volume.restrict (ball y s)) := by
    simpa only [smul_eq_mul, Function.comp_def] using htransport.symm.trans hscalar
  rw [hnorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  have hs3 : 0 ≤ s^3 := (pow_pos hs 3).le
  simp only [c, ENNReal.toReal_ofReal (inv_nonneg.mpr hs3)]
  norm_num

/-- Local smoothness supplies the measurability needed in the preceding
physical-ball change of variables. -/
theorem aestronglyMeasurable_physicalBall_of_contDiffAt_closedBall
    (F : R3 → ℝ) (y : R3) (s : ℝ)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ 45 F x) :
    AEStronglyMeasurable F (volume.restrict (ball y s)) := by
  have hcont : ContinuousOn F (closedBall y s) :=
    continuousOn_of_forall_continuousAt fun x hx => (hF x hx).continuousAt
  exact hcont.aestronglyMeasurable_of_subset_isCompact
    (isCompact_closedBall y s) measurableSet_ball ball_subset_closedBall

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation

namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- The complete finite-order Taylor/L² estimate up to the finite Schwarz
symmetry identity. Its constant is uniform in the function, center and scale,
and the L² norm is on the actual physical ball. -/
theorem exists_uniform_taylor44_jet_le_physicalBall_L2_of_symmetric :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : R3 → ℝ) (y : R3) (s M : ℝ)
      (j : ℕ), 0 < s → 0 ≤ M →
      (∀ x ∈ closedBall y s, ContDiffAt ℝ 45 F x) →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ 45 F x‖ ≤ M) →
      (∀ k : ℕ, k ≤ 44 → ∀ (v : Fin k → R3) (σ : Equiv.Perm (Fin k)),
        iteratedFDeriv ℝ k F y (v ∘ σ) = iteratedFDeriv ℝ k F y v) →
      j ≤ 10 →
      s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
        C * (((s^3)⁻¹)^((1 : ℝ)/2) *
          (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^45) := by
  obtain ⟨Cp,hCp,hPoly⟩ := exists_uniform_taylor44_polynomial_deriv_le_unitBall_L2
  let μ : Measure R3 := volume.restrict (ball (0 : R3) 1)
  let V : ℝ := μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)
  have hV0 : 0 ≤ V := by
    dsimp [V]
    positivity
  refine ⟨Cp * (V+1), mul_pos hCp (by linarith), ?_⟩
  intro F y s M j hs hM0 hF hM hSym hj
  have hFscaledLp := memLp_affine_unitBall_of_contDiffAt_closedBall F y s hs hF
  have hL2 := lpNorm_taylor44_le_affine_lpNorm_add_remainder
    F y s M hs hM0 hF hM hFscaledLp
  have hFmeas := aestronglyMeasurable_physicalBall_of_contDiffAt_closedBall F y s hF
  have hscale := eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall_local
    F y s hs hFmeas
  have hpoly := hPoly F y s j hj
  have hjet := iteratedFDeriv_taylor44_at_zero_of_symmetric F y s j
    (by omega : j ≤ 44) hSym
  have hpow : 0 ≤ s^j := (pow_pos hs _).le
  have hN0 : 0 ≤ (eLpNorm F 2 (volume.restrict (ball y s))).toReal :=
    ENNReal.toReal_nonneg
  have hX0 : 0 ≤ ((s^3)⁻¹)^((1 : ℝ)/2) *
      (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by positivity
  have hY0 : 0 ≤ M*s^45 := mul_nonneg hM0 (pow_nonneg hs.le _)
  have hjetnorm : ‖iteratedFDeriv ℝ j (taylor44 F y s) (0 : R3)‖ =
      s^j * ‖iteratedFDeriv ℝ j F y‖ := by
    rw [hjet, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpow]
  have hN : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      Cp * (((s^3)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal +
        M*s^45*V) := by
    calc
      _ = ‖iteratedFDeriv ℝ j (taylor44 F y s) (0 : R3)‖ := hjetnorm.symm
      _ ≤ Cp * (eLpNorm (taylor44 F y s) 2 μ).toReal := hpoly
      _ ≤ Cp * ((eLpNorm (fun z : R3 => F (y+s•z)) 2 μ).toReal +
          M*s^45*V) := mul_le_mul_of_nonneg_left hL2 hCp.le
      _ = _ := by rw [hscale]
  calc
    s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      Cp * (((s^3)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal +
        M*s^45*V) := hN
    _ ≤ Cp * (V+1) *
      (((s^3)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^45) := by
      nlinarith [mul_nonneg hCp.le hX0, mul_nonneg hCp.le hY0,
        mul_nonneg hV0 hX0, mul_nonneg hV0 hY0]

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation


namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

/-- Actual local smoothness discharges finite Schwarz symmetry in the
physical-ball Taylor/L² interpolation estimate. -/
theorem exists_uniform_taylor44_jet_le_physicalBall_L2_of_contDiffOn :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : R3 → ℝ) (U : Set R3)
      (y : R3) (s M : ℝ) (j : ℕ),
      IsOpen U → ContDiffOn ℝ ∞ F U → y ∈ U →
      closedBall y s ⊆ U → 0 < s → 0 ≤ M →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ 45 F x‖ ≤ M) →
      j ≤ 10 →
      s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
        C * (((s^3)⁻¹)^((1 : ℝ)/2) *
          (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^45) := by
  obtain ⟨C,hC,hInterp⟩ :=
    exists_uniform_taylor44_jet_le_physicalBall_L2_of_symmetric
  refine ⟨C,hC,?_⟩
  intro F U y s M j hU hF hy hBall hs hM0 hM hj
  have h45 : (45 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((45 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hF45 : ∀ x ∈ closedBall y s, ContDiffAt ℝ 45 F x := by
    intro x hx
    exact (hF.contDiffAt (hU.mem_nhds (hBall hx))).of_le h45
  exact hInterp F y s M j hs hM0 hF45 hM
    (fun k _hk v σ =>
      iteratedFDeriv_comp_perm_of_contDiffOn_open F U hU hF y hy k v σ)
    hj

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation


namespace OAI.AnisotropicCalderon.LocalPolynomialInterpolation
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

/-- The Section 06 choice s=r^(1/23), m=45 and j≤10 yields the genuine
three-halves derivative gain from a physical-ball L² bound of order r². -/
theorem exists_uniform_taylor44_jet_le_three_halves_of_local_L2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : R3 → ℝ) (U : Set R3)
      (y : R3) (r A M : ℝ) (j : ℕ),
      IsOpen U → ContDiffOn ℝ ∞ F U → y ∈ U →
      0 < r → r ≤ 1 → 0 ≤ A → 0 ≤ M →
      closedBall y (r ^ ((1 : ℝ)/23)) ⊆ U →
      (∀ x ∈ closedBall y (r ^ ((1 : ℝ)/23)),
        ‖iteratedFDeriv ℝ 45 F x‖ ≤ M) →
      (eLpNorm F 2
        (volume.restrict (ball y (r ^ ((1 : ℝ)/23))))).toReal ≤ A*r^2 →
      j ≤ 10 →
      ‖iteratedFDeriv ℝ j F y‖ ≤ C*(A+M)*r^(3/2 : ℝ) := by
  obtain ⟨C,hC,hInterp⟩ :=
    exists_uniform_taylor44_jet_le_physicalBall_L2_of_contDiffOn
  refine ⟨C,hC,?_⟩
  intro F U y r A M j hU hF hy hr hr1 hA0 hM0 hBall hM hL2 hj
  let s : ℝ := r ^ ((1 : ℝ)/23)
  let qA : ℝ := r ^ ((2 : ℝ) - ((j : ℝ) + 3/2)/23)
  let qB : ℝ := r ^ (((45 : ℝ) - (j : ℝ))/23)
  let scale : ℝ := ((s^3)⁻¹)^((1 : ℝ)/2)
  have hs : 0 < s := Real.rpow_pos_of_pos hr _
  have hsj : 0 < s^j := pow_pos hs _
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hBridge := hInterp F U y s M j hU hF hy hBall hs hM0 hM hj
  have hL2' : (eLpNorm F 2 (volume.restrict (ball y s))).toReal ≤ A*r^2 := hL2
  have hN : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      C*(scale*(A*r^2)+M*s^45) := by
    exact hBridge.trans <|
      mul_le_mul_of_nonneg_left
        (add_le_add_left (mul_le_mul_of_nonneg_left hL2' hscale0) _) hC.le
  have hPowA : s^j * qA = scale*r^2 := by
    simpa [s, qA, scale] using interpolation_scale_L2_power r hr j
  have hPowB : s^j * qB = s^45 := by
    simpa [s, qB] using interpolation_scale_remainder_power r hr j
  have hBound : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      s^j*(C*(A*qA+M*qB)) := by
    calc
      _ ≤ C*(scale*(A*r^2)+M*s^45) := hN
      _ = C*(A*(scale*r^2)+M*s^45) := by ring
      _ = C*(A*(s^j*qA)+M*(s^j*qB)) := by rw [hPowA, hPowB]
      _ = s^j*(C*(A*qA+M*qB)) := by ring
  have hCancel : ‖iteratedFDeriv ℝ j F y‖ ≤ C*(A*qA+M*qB) :=
    le_of_mul_le_mul_left hBound hsj
  have hExp :=
    OAI.AnisotropicCalderon.MixedKernelConstructionTask.actual_interpolation_powers_le_three_halves
      r hr hr1 j hj
  have hExpA : qA ≤ r^(3/2 : ℝ) := hExp.1
  have hExpB : qB ≤ r^(3/2 : ℝ) := hExp.2
  calc
    ‖iteratedFDeriv ℝ j F y‖ ≤ C*(A*qA+M*qB) := hCancel
    _ ≤ C*((A+M)*r^(3/2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      calc
        A*qA+M*qB ≤ A*r^(3/2 : ℝ)+M*r^(3/2 : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hExpA hA0)
            (mul_le_mul_of_nonneg_left hExpB hM0)
        _ = (A+M)*r^(3/2 : ℝ) := by ring
    _ = C*(A+M)*r^(3/2 : ℝ) := by ring

end OAI.AnisotropicCalderon.LocalPolynomialInterpolation
