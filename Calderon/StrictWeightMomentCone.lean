import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-! Native physical-coordinate factor moment cones for the original product Hessian split.
Before-source authority: Root7156253f; exact ALL14 inventory and weighted expansion v004–v006.
This coherent owner has exactly three definitions and three ordinary proof roots.
The product covariance/rank-one/K/native endpoint remains a separate explicit remainder. -/
set_option autoImplicit false
noncomputable section
open Set Metric Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ProductHessianSeparation

local notation "V3" => (Fin 3 → ℝ)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "SA3" => selfAdjoint (Matrix (Fin 3) (Fin 3) ℝ)

def metricTangentSphere (G : M3) (ell a : V3) : Set V3 :=
  {v | dotProduct ell v = 0 ∧
    dotProduct v (G *ᵥ v) = dotProduct a (G *ᵥ a)}

def strictSphereCone (G : M3) (ell a : V3) : Set SA3 :=
  {P | ∀ v ∈ metricTangentSphere G ell a,
    0 < dotProduct a ((P : M3) *ᵥ a) + dotProduct v ((P : M3) *ᵥ v)}

def metricMomentCondition (G : M3) (ell a : V3) (D : M3) : Prop :=
  let d : ℝ := dotProduct ell (D *ᵥ ell)
  let S : M3 := D - d • Matrix.vecMulVec a a
  D.IsHermitian ∧ 0 ≤ d ∧ S.PosSemidef ∧ S *ᵥ ell = 0 ∧
    Matrix.trace (G * S) = d * dotProduct a (G *ᵥ a)

theorem exists_unique_selfAdjoint_trace_pairing
    {n : Type*} [Fintype n] [DecidableEq n]
    (f : selfAdjoint (Matrix n n ℝ) →L[ℝ] ℝ) :
    ∃! D : selfAdjoint (Matrix n n ℝ),
      ∀ P : selfAdjoint (Matrix n n ℝ),
        f P = Matrix.trace ((P : Matrix n n ℝ) * (D : Matrix n n ℝ)) := by
  classical
  let q : Matrix n n ℝ →L[ℝ] selfAdjoint (Matrix n n ℝ) :=
    selfAdjointPartL ℝ (Matrix n n ℝ)
  let F : Matrix n n ℝ →L[ℝ] ℝ := f.comp q
  let c : Matrix n n ℝ := Matrix.of fun i j => F (Matrix.single i j 1)
  have hq (A : Matrix n n ℝ) :
      (q A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A + Aᴴ) := by
    change (selfAdjointPart ℝ A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A+Aᴴ)
    simp only [selfAdjointPart_apply_coe,invOf_eq_inv,Matrix.star_eq_conjTranspose]
  have hqSingle (i j : n) : q (Matrix.single i j 1) = q (Matrix.single j i 1) := by
    apply Subtype.ext
    rw [hq,hq,Matrix.conjTranspose_single,Matrix.conjTranspose_single]
    simp only [star_one]
    rw [add_comm]
  have hc (i j : n) : c j i = c i j := by
    change f (q (Matrix.single j i 1)) = f (q (Matrix.single i j 1))
    rw [hqSingle j i]
  have hcHermitian : c.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hc i j
  let D : selfAdjoint (Matrix n n ℝ) := ⟨c,hcHermitian⟩
  have hF (A : Matrix n n ℝ) :
      F A = ∑ i : n, ∑ j : n, A i j * F (Matrix.single i j 1) := by
    calc
      F A = F (∑ i : n, ∑ j : n, Matrix.single i j (A i j)) := by
        rw [← Matrix.matrix_eq_sum_single A]
      _ = ∑ i : n, ∑ j : n, A i j * F (Matrix.single i j 1) := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hSingle : Matrix.single i j (A i j) =
            (A i j) • Matrix.single i j (1 : ℝ) := by
          rw [Matrix.smul_single]
          simp only [smul_eq_mul,mul_one]
        rw [hSingle,map_smul]
        rfl
  have hRep (P : selfAdjoint (Matrix n n ℝ)) :
      f P = Matrix.trace ((P : Matrix n n ℝ) * c) := by
    have hqP : q (P : Matrix n n ℝ) = P := P.2.selfAdjointPart_apply ℝ
    calc
      f P = F (P : Matrix n n ℝ) := by
        change f P = f (q (P : Matrix n n ℝ))
        rw [hqP]
      _ = ∑ i : n, ∑ j : n, (P : Matrix n n ℝ) i j * c i j := hF _
      _ = Matrix.trace ((P : Matrix n n ℝ) * c) := by
        simp only [Matrix.trace,Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (P : Matrix n n ℝ) i j*c i j = (P : Matrix n n ℝ) i j*c j i
        rw [hc i j]
  have hTraceSingle (P : selfAdjoint (Matrix n n ℝ)) (i j : n) :
      Matrix.trace ((q (Matrix.single i j 1) : Matrix n n ℝ) * (P : Matrix n n ℝ)) =
        (P : Matrix n n ℝ) i j := by
    rw [hq,Matrix.conjTranspose_single]
    simp only [star_one,Matrix.smul_mul,Matrix.add_mul,Matrix.trace_smul,
      Matrix.trace_add,Matrix.trace_single_mul,smul_eq_mul,one_mul]
    have hSym : (P : Matrix n n ℝ) j i = (P : Matrix n n ℝ) i j := by
      exact P.2.isHermitian.isSymm.apply i j
    rw [hSym]
    ring
  refine ⟨D,hRep,?_⟩
  intro D' hD'
  apply Subtype.ext
  ext i j
  have h := (hD' (q (Matrix.single i j 1))).symm.trans (hRep (q (Matrix.single i j 1)))
  change Matrix.trace ((q (Matrix.single i j 1) : Matrix n n ℝ)*(D' : Matrix n n ℝ)) =
    Matrix.trace ((q (Matrix.single i j 1) : Matrix n n ℝ)*(D : Matrix n n ℝ)) at h
  rw [hTraceSingle D' i j,hTraceSingle D i j] at h
  exact h

theorem metricMomentCondition_iff_sum_generators
    (G : M3) (hG : G.PosDef) (ell a : V3) (ha : dotProduct ell a = 1) (D : M3) :
    metricMomentCondition G ell a D ↔
      ∃ (w : Fin 3 → ℝ) (v : Fin 3 → V3),
        (∀ j, 0 ≤ w j) ∧ (∀ j, v j ∈ metricTangentSphere G ell a) ∧
        (∑ j, w j) = dotProduct ell (D *ᵥ ell) ∧
        D = ∑ j, w j • (Matrix.vecMulVec a a + Matrix.vecMulVec (v j) (v j)) := by
  classical
  let A : ℝ := dotProduct a (G *ᵥ a)
  have haNe : a ≠ 0 := by
    intro h
    simp only [h,dotProduct_zero] at ha
    norm_num at ha
  have hA : 0 < A := by
    simpa only [A,star_trivial] using hG.dotProduct_mulVec_pos haNe
  have hRankPSD (v : V3) : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  have hRankTrace (v : V3) :
      Matrix.trace (G * Matrix.vecMulVec v v) = dotProduct v (G *ᵥ v) := by
    rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  have hRankQuad (v : V3) :
      dotProduct ell (Matrix.vecMulVec v v *ᵥ ell) = (dotProduct ell v)^2 := by
    simp only [dotProduct,Matrix.mulVec,Matrix.vecMulVec_apply,Fin.sum_univ_three]
    ring
  have hRankKer (v : V3) (hv : dotProduct ell v = 0) :
      Matrix.vecMulVec v v *ᵥ ell = 0 := by
    ext i
    have h : (Matrix.vecMulVec v v *ᵥ ell) i = v i * dotProduct ell v := by
      simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Fin.sum_univ_three]
      ring
    rw [h,hv,mul_zero]
    rfl
  constructor
  · intro hMoment
    let d : ℝ := dotProduct ell (D *ᵥ ell)
    let S : M3 := D - d • Matrix.vecMulVec a a
    change D.IsHermitian ∧ 0 ≤ d ∧ S.PosSemidef ∧ S *ᵥ ell = 0 ∧
      Matrix.trace (G*S) = d*A at hMoment
    obtain ⟨hDH,hd,hS,hKer,hTrace⟩ := hMoment
    have hEllNe : ell ≠ 0 := by
      intro h
      simp only [h,zero_dotProduct] at ha
      norm_num at ha
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hEllNe
    have hi' : ell i ≠ 0 := hi
    obtain ⟨j,hji⟩ := exists_ne i
    let e : V3 := fun k => if k=j then ell i else if k=i then -ell j else 0
    have heEll : dotProduct ell e = 0 := by
      have hE : e = ell i • Pi.single j (1 : ℝ) - ell j • Pi.single i 1 := by
        ext k
        by_cases hkj : k=j
        · subst k
          simp [e,hji,hji.symm]
        · by_cases hki : k=i
          · subst k
            simp [e,hji,hji.symm]
          · simp [e,hkj,hki]
      rw [hE]
      simp only [dotProduct_sub,dotProduct_smul,dotProduct_single_one,smul_eq_mul]
      ring
    have heNe : e ≠ 0 := by
      intro h
      have hj : ell i = 0 := by
        simpa only [e,if_pos rfl,Pi.zero_apply] using congrFun h j
      exact hi' hj
    have heG : 0 < dotProduct e (G *ᵥ e) := by
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos heNe
    let vstar : V3 := Real.sqrt (A/dotProduct e (G *ᵥ e)) • e
    have hVstar : vstar ∈ metricTangentSphere G ell a := by
      refine ⟨?_,?_⟩
      · simp only [vstar,dotProduct_smul,smul_eq_mul,heEll,mul_zero]
      · have hScale : dotProduct vstar (G *ᵥ vstar) =
            (Real.sqrt (A/dotProduct e (G *ᵥ e)))^2 * dotProduct e (G *ᵥ e) := by
          simp only [vstar,dotProduct,Matrix.mulVec,Pi.smul_apply,smul_eq_mul,
            Fin.sum_univ_three]
          ring
        rw [hScale,Real.sq_sqrt (div_nonneg hA.le heG.le),div_mul_cancel₀ _ heG.ne']
    let lam : Fin 3 → ℝ := hS.isHermitian.eigenvalues
    let u : Fin 3 → V3 := fun k => (hS.isHermitian.eigenvectorBasis k : V3)
    have hLam (k : Fin 3) : 0 ≤ lam k := hS.eigenvalues_nonneg k
    have hUne (k : Fin 3) : u k ≠ 0 := by
      intro h
      apply hS.isHermitian.eigenvectorBasis.orthonormal.ne_zero k
      apply PiLp.ext
      intro i
      exact congrFun h i
    have hEig (k : Fin 3) : S *ᵥ u k = lam k • u k :=
      hS.isHermitian.mulVec_eigenvectorBasis k
    have hUG (k : Fin 3) : 0 < dotProduct (u k) (G *ᵥ u k) := by
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos (hUne k)
    have hUEll (k : Fin 3) (hk : 0 < lam k) : dotProduct ell (u k) = 0 := by
      have hComm := hS.isHermitian.star_dotProduct_mulVec_comm ell (u k)
      simp only [star_trivial,hKer,dotProduct_zero] at hComm
      rw [hEig,dotProduct_smul,smul_eq_mul] at hComm
      exact (mul_eq_zero.mp hComm).resolve_left hk.ne'
    have hSEntry (i j : Fin 3) : S i j = ∑ k, lam k * u k i * u k j := by
      have hSpec := hS.isHermitian.spectral_theorem
      rw [hSpec]
      simp only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
        Matrix.mul_apply,Matrix.diagonal_apply,Matrix.of_apply,Matrix.conjTranspose_apply,star_trivial,
        Matrix.IsHermitian.eigenvectorUnitary_apply,RCLike.ofReal_real_eq_id,
        Function.comp_apply,id_eq,lam,u,Fin.sum_univ_three]
      norm_num <;> ring
    have hSpectral : S = ∑ k, lam k • Matrix.vecMulVec (u k) (u k) := by
      ext i j
      simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.vecMulVec_apply,mul_assoc] using hSEntry i j
    have hTraceSpectral : Matrix.trace (G*S) =
        ∑ k, lam k * dotProduct (u k) (G *ᵥ u k) := by
      rw [hSpectral]
      simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,hRankTrace]
    let w : Fin 3 → ℝ := fun k => lam k * dotProduct (u k) (G *ᵥ u k) / A
    let v : Fin 3 → V3 := fun k => if 0 < lam k then
      Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) • u k else vstar
    have hw (k : Fin 3) : 0 ≤ w k :=
      div_nonneg (mul_nonneg (hLam k) (hUG k).le) hA.le
    have hv (k : Fin 3) : v k ∈ metricTangentSphere G ell a := by
      by_cases hk : 0 < lam k
      · rw [show v k = Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) • u k from if_pos hk]
        refine ⟨?_,?_⟩
        · simp only [dotProduct_smul,smul_eq_mul,hUEll k hk,mul_zero]
        · have hScale (t : ℝ) : dotProduct (t • u k) (G *ᵥ (t • u k)) =
              t^2 * dotProduct (u k) (G *ᵥ u k) := by
            simp only [dotProduct,Matrix.mulVec,Pi.smul_apply,smul_eq_mul,
              Fin.sum_univ_three]
            ring
          rw [hScale,Real.sq_sqrt (div_nonneg hA.le (hUG k).le),
            div_mul_cancel₀ _ (hUG k).ne']
      · simpa only [v,if_neg hk] using hVstar
    have hCov (k : Fin 3) :
        w k • Matrix.vecMulVec (v k) (v k) = lam k • Matrix.vecMulVec (u k) (u k) := by
      by_cases hk : 0 < lam k
      · have hFactor : w k * (Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)))^2 = lam k := by
          rw [Real.sq_sqrt (div_nonneg hA.le (hUG k).le)]
          dsimp only [w]
          field_simp [hA.ne',(hUG k).ne']
          <;> ring
        ext i j
        change w k * (v k i * v k j) = lam k * (u k i * u k j)
        rw [show v k = Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) • u k from if_pos hk]
        simp only [Pi.smul_apply,smul_eq_mul]
        calc
          w k * ((Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) * u k i) *
              (Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)) * u k j)) =
              (w k * (Real.sqrt (A/dotProduct (u k) (G *ᵥ u k)))^2) * (u k i*u k j) := by ring
          _ = lam k * (u k i*u k j) := by rw [hFactor]
      · have hZero : lam k = 0 := le_antisymm (le_of_not_gt hk) (hLam k)
        simp only [w,hZero,zero_mul,zero_div,zero_smul]
    have hWeights : ∑ k, w k = d := by
      calc
        ∑ k, w k = (∑ k, lam k * dotProduct (u k) (G *ᵥ u k))/A := by
          simp only [w,Finset.sum_div]
        _ = (d*A)/A := by rw [← hTraceSpectral,hTrace]
        _ = d := mul_div_cancel_right₀ _ hA.ne'
    have hWsum : ∑ k, w k • Matrix.vecMulVec (v k) (v k) = S := by
      rw [hSpectral]
      apply Finset.sum_congr rfl
      intro k _
      exact hCov k
    refine ⟨w,v,hw,hv,hWeights,?_⟩
    rw [show D = d • Matrix.vecMulVec a a + S by dsimp only [S]; abel]
    symm
    calc
      (∑ k, w k • (Matrix.vecMulVec a a + Matrix.vecMulVec (v k) (v k))) =
          (∑ k, w k) • Matrix.vecMulVec a a + ∑ k, w k • Matrix.vecMulVec (v k) (v k) := by
        simp only [smul_add,Finset.sum_add_distrib,Finset.sum_smul]
      _ = d • Matrix.vecMulVec a a + S := by rw [hWeights,hWsum]
  · rintro ⟨w,v,hw,hv,hWeights,hDecomp⟩
    let d : ℝ := dotProduct ell (D *ᵥ ell)
    let S : M3 := D - d • Matrix.vecMulVec a a
    have hd : d = ∑ k, w k := hWeights.symm
    have hSdecomp : S = ∑ k, w k • Matrix.vecMulVec (v k) (v k) := by
      dsimp only [S]
      rw [hDecomp,hd]
      ext i j
      simp only [Fin.sum_univ_three,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
        smul_eq_mul]
      ring
    have hDpsd : D.PosSemidef := by
      rw [hDecomp,Fin.sum_univ_three]
      simpa only [add_assoc] using
        (((hRankPSD a).add (hRankPSD (v 0))).smul (hw 0)).add
          ((((hRankPSD a).add (hRankPSD (v 1))).smul (hw 1)).add
            (((hRankPSD a).add (hRankPSD (v 2))).smul (hw 2)))
    have hSpsd : S.PosSemidef := by
      rw [hSdecomp,Fin.sum_univ_three]
      simpa only [add_assoc] using
        ((hRankPSD (v 0)).smul (hw 0)).add
          (((hRankPSD (v 1)).smul (hw 1)).add ((hRankPSD (v 2)).smul (hw 2)))
    have hSk : S *ᵥ ell = 0 := by
      rw [hSdecomp,Fin.sum_univ_three]
      simp only [Matrix.add_mulVec,Matrix.smul_mulVec,
        hRankKer (v 0) (hv 0).1,hRankKer (v 1) (hv 1).1,hRankKer (v 2) (hv 2).1,
        smul_zero,add_zero]
    have hSt : Matrix.trace (G*S) = d*A := by
      rw [hSdecomp,Fin.sum_univ_three]
      simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
        smul_eq_mul,hRankTrace,(hv 0).2,(hv 1).2,(hv 2).2]
      rw [hd,Fin.sum_univ_three]
      ring
    have hdNonneg : 0 ≤ d := by
      rw [hd]
      exact Finset.sum_nonneg (fun k _ => hw k)
    change D.IsHermitian ∧ 0 ≤ d ∧ S.PosSemidef ∧ S *ᵥ ell = 0 ∧
      Matrix.trace (G*S) = d*A
    exact ⟨hDpsd.isHermitian,hdNonneg,hSpsd,hSk,hSt⟩

theorem metricMomentCondition_closed_convex_dual
    (G : M3) (hG : G.PosDef) (ell a : V3) (ha : dotProduct ell a = 1) :
    IsClosed {D : SA3 | metricMomentCondition G ell a (D : M3)} ∧
    Convex ℝ {D : SA3 | metricMomentCondition G ell a (D : M3)} ∧
    IsOpen (strictSphereCone G ell a) ∧ Convex ℝ (strictSphereCone G ell a) ∧
    (strictSphereCone G ell a).Nonempty ∧
    (∀ D : SA3,
      (∀ P ∈ strictSphereCone G ell a, 0 ≤ Matrix.trace ((P : M3) * (D : M3))) ↔
        metricMomentCondition G ell a (D : M3)) := by
  classical
  letI : ContinuousSMul ℝ SA3 :=
    Topology.IsInducing.continuousSMul
      (M := ℝ) (X := M3) (Y := SA3)
      (g := fun D : SA3 => (D : M3)) (f := fun t : ℝ => t)
      Topology.IsInducing.subtypeVal continuous_id (fun {_ _} => rfl)
  letI : LocallyConvexSpace ℝ M3 :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin 3 → Fin 3 → ℝ))
  let coeL : SA3 →ₗ[ℝ] M3 :=
    { toFun := fun D : SA3 => (D : M3)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : LocallyConvexSpace ℝ SA3 :=
    Topology.IsInducing.locallyConvexSpace (f := coeL)
      Topology.IsInducing.subtypeVal
  let A : ℝ := dotProduct a (G *ᵥ a)
  let d : SA3 → ℝ := fun D => dotProduct ell ((D : M3) *ᵥ ell)
  let S : SA3 → M3 := fun D => (D : M3) - d D • Matrix.vecMulVec a a
  have haNe : a ≠ 0 := by
    intro h
    simp only [h,dotProduct_zero] at ha
    norm_num at ha
  have hA : 0 < A := by
    simpa only [A,star_trivial] using hG.dotProduct_mulVec_pos haNe
  have hRankPSD (v : V3) : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  have hTraceRank (P : M3) (v : V3) :
      Matrix.trace (P * Matrix.vecMulVec v v) = dotProduct v (P *ᵥ v) := by
    rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  have hMom (D : SA3) : metricMomentCondition G ell a (D : M3) ↔
      0 ≤ d D ∧ (S D).PosSemidef ∧ S D *ᵥ ell = 0 ∧ Matrix.trace (G*S D) = d D*A := by
    have hHermitian : (D : M3).IsHermitian := D.2
    simp only [metricMomentCondition,d,S,A,hHermitian,true_and]
  have hEntry (i j : Fin 3) : Continuous (fun D : SA3 => (D : M3) i j) :=
    Continuous.comp (f := fun D : SA3 => (D : M3))
      (g := fun B : M3 => B i j) (continuous_apply_apply i j) continuous_subtype_val
  have hdContinuous : Continuous d := by
    have hRow (i : Fin 3) : Continuous (fun D : SA3 => ∑ j : Fin 3, (D : M3) i j*ell j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hEntry i j).mul_const (ell j))
    change Continuous (fun D : SA3 => ∑ i : Fin 3, ell i*(∑ j : Fin 3, (D : M3) i j*ell j))
    exact continuous_finsetSum Finset.univ (fun i _ => (hRow i).const_mul (ell i))
  have hSContinuous : Continuous S := by
    exact continuous_subtype_val.sub (hdContinuous.smul continuous_const)
  have hPSDClosed : IsClosed {T : M3 | T.PosSemidef} := by
    have hSet : {T : M3 | T.PosSemidef} =
        {T : M3 | T.IsHermitian} ∩ ⋂ v : V3, {T : M3 | 0 ≤ dotProduct v (T *ᵥ v)} := by
      ext T
      simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,
        Matrix.posSemidef_iff_dotProduct_mulVec,star_trivial]
    rw [hSet]
    apply IsClosed.inter
    · change IsClosed {T : M3 | Tᴴ = T}
      exact isClosed_eq (by fun_prop) continuous_id
    · apply isClosed_iInter
      intro v
      apply isClosed_le continuous_const
      simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_three]
      fun_prop
  have hClosed : IsClosed {D : SA3 | metricMomentCondition G ell a (D : M3)} := by
    have hKernel : IsClosed {D : SA3 | S D *ᵥ ell = 0} :=
      isClosed_eq (by
        change Continuous (fun D : SA3 => S D *ᵥ ell)
        apply continuous_pi
        intro i
        have hSentry (j : Fin 3) : Continuous (fun D : SA3 => S D i j) :=
          Continuous.comp (f := S) (g := fun B : M3 => B i j)
            (continuous_apply_apply i j) hSContinuous
        change Continuous (fun D : SA3 => ∑ j, S D i j*ell j)
        simp only [Fin.sum_univ_three]
        fun_prop) continuous_const
    have hTrace : IsClosed {D : SA3 | Matrix.trace (G*S D) = d D*A} := by
      apply isClosed_eq
      · simp only [Matrix.trace,Matrix.mul_apply,Fin.sum_univ_three]
        fun_prop
      · exact hdContinuous.mul_const A
    have hdNonneg : IsClosed {D : SA3 | (0 : ℝ) ≤ d D} :=
      isClosed_le (f := fun _ : SA3 => (0 : ℝ)) (g := d)
        continuous_const hdContinuous
    have hResult := (hdNonneg.inter (hPSDClosed.preimage hSContinuous)).inter
      (hKernel.inter hTrace)
    convert hResult using 1
    ext D
    simp only [mem_setOf_eq,mem_inter_iff,mem_preimage,hMom,and_assoc]
  have hdAdd (D E : SA3) : d (D+E) = d D+d E := by
    change dotProduct ell (((D : M3)+(E : M3))*ᵥ ell) = _
    simp only [Matrix.add_mulVec,dotProduct_add]
    rfl
  have hdSmul (t : ℝ) (D : SA3) : d (t • D) = t*d D := by
    change dotProduct ell ((t • (D : M3))*ᵥ ell) = _
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    rfl
  have hSAdd (D E : SA3) : S (D+E) = S D+S E := by
    dsimp only [S]
    rw [hdAdd]
    ext i j
    change (D : M3) i j+(E : M3) i j-(d D+d E)*(a i*a j) =
      ((D : M3) i j-d D*(a i*a j))+((E : M3) i j-d E*(a i*a j))
    ring
  have hSSmul (t : ℝ) (D : SA3) : S (t • D) = t • S D := by
    dsimp only [S]
    rw [hdSmul]
    ext i j
    change t*(D : M3) i j-(t*d D)*(a i*a j) = t*((D : M3) i j-d D*(a i*a j))
    ring
  have hScaleMom (t : ℝ) (ht : 0 ≤ t) (D : SA3)
      (hD : metricMomentCondition G ell a (D : M3)) :
      metricMomentCondition G ell a ((t • D : SA3) : M3) := by
    obtain ⟨hd,hPSD,hKer,hTrace⟩ := (hMom D).mp hD
    apply (hMom (t • D)).mpr
    rw [hdSmul,hSSmul]
    refine ⟨mul_nonneg ht hd,hPSD.smul ht,?_,?_⟩
    · simp only [Matrix.smul_mulVec,hKer,smul_zero]
    · rw [Matrix.mul_smul,Matrix.trace_smul,hTrace]
      change t*(d D*A) = (t*d D)*A
      ring
  have hConvex : Convex ℝ {D : SA3 | metricMomentCondition G ell a (D : M3)} := by
    intro D hD E hE t s ht hs hts
    obtain ⟨hdD,hPSDd,hKd,hTd⟩ := (hMom D).mp hD
    obtain ⟨hdE,hPSDe,hKe,hTe⟩ := (hMom E).mp hE
    apply (hMom (t • D+s • E)).mpr
    rw [hdAdd,hdSmul,hdSmul,hSAdd,hSSmul,hSSmul]
    refine ⟨add_nonneg (mul_nonneg ht hdD) (mul_nonneg hs hdE),
      (hPSDd.smul ht).add (hPSDe.smul hs),?_,?_⟩
    · simp only [Matrix.add_mulVec,Matrix.smul_mulVec,hKd,hKe,smul_zero,add_zero]
    · rw [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,Matrix.trace_add,
        Matrix.trace_smul,Matrix.trace_smul,hTd,hTe]
      change t*(d D*A)+s*(d E*A) = (t*d D+s*d E)*A
      ring
  have hZeroMom : metricMomentCondition G ell a ((0 : SA3) : M3) := by
    simp [metricMomentCondition,Matrix.PosSemidef.zero]
  have hCompactSphere : IsCompact (metricTangentSphere G ell a) := by
    have hQuadContinuous : Continuous (fun v : V3 => dotProduct v (G *ᵥ v)) := by
      simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_three]
      fun_prop
    have hPositive (v : V3) (hv : v ≠ 0) : 0 < dotProduct v (G *ᵥ v) := by
      simpa only [star_trivial] using hG.dotProduct_mulVec_pos hv
    obtain ⟨beta,hbeta,hMin⟩ := (isCompact_sphere (0 : V3) 1).exists_forall_le'
      hQuadContinuous.continuousOn (fun v hv => hPositive v (by
        have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
        intro h
        simp only [h,norm_zero] at hn
        norm_num at hn))
    have hLower (v : V3) : beta*‖v‖^2 ≤ dotProduct v (G *ᵥ v) := by
      by_cases hv : v=0
      · subst v
        simp
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let w : V3 := ‖v‖⁻¹ • v
      have hw : ‖w‖ = 1 := by
        simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
          inv_mul_cancel₀ hn.ne']
      have hMinw := hMin w (by simpa only [Metric.mem_sphere,dist_zero_right] using hw)
      have hBack : ‖v‖ • w = v := by
        simp only [w,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
      have hScale : dotProduct v (G *ᵥ v) = ‖v‖^2 * dotProduct w (G *ᵥ w) := by
        nth_rw 1 [← hBack]
        nth_rw 2 [← hBack]
        simp only [dotProduct,Matrix.mulVec,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three]
        ring
      rw [hScale,mul_comm beta (‖v‖^2)]
      exact mul_le_mul_of_nonneg_left hMinw (sq_nonneg ‖v‖)
    have hClosedSphere : IsClosed (metricTangentSphere G ell a) := by
      apply IsClosed.inter
      · apply isClosed_eq
        · change Continuous (fun v : V3 => dotProduct ell v)
          simp only [dotProduct,Fin.sum_univ_three]
          fun_prop
        · exact continuous_const
      · exact isClosed_eq hQuadContinuous continuous_const
    have hBound (v : V3) (hv : v ∈ metricTangentSphere G ell a) : ‖v‖ ≤ A/beta+1 := by
      have hL := hLower v
      rw [hv.2] at hL
      have hSq : ‖v‖^2 ≤ A/beta := by
        apply (le_div_iff₀ hbeta).mpr
        simpa only [mul_comm] using hL
      nlinarith only [hSq,sq_nonneg (‖v‖-(1/2 : ℝ))]
    apply isCompact_iff_isClosed_bounded.mpr
    refine ⟨hClosedSphere,?_⟩
    apply (Metric.isBounded_closedBall (x := (0 : V3)) (r := A/beta+1)).subset
    intro v hv
    apply Metric.mem_closedBall.mpr
    simpa only [dist_zero_right] using hBound v hv
  let phi : SA3 → V3 → ℝ := fun P v =>
    dotProduct a ((P : M3)*ᵥ a)+dotProduct v ((P : M3)*ᵥ v)
  have hJoint : Continuous (fun z : SA3 × V3 => phi z.1 z.2) := by
    have hPentry (i j : Fin 3) : Continuous (fun z : SA3 × V3 => (z.1 : M3) i j) :=
      Continuous.comp (f := fun z : SA3 × V3 => z.1)
        (g := fun P : SA3 => (P : M3) i j) (hEntry i j) continuous_fst
    have hVentry (i : Fin 3) : Continuous (fun z : SA3 × V3 => z.2 i) :=
      Continuous.comp (f := fun z : SA3 × V3 => z.2)
        (g := fun v : V3 => v i) (continuous_apply i) continuous_snd
    have hFixedRow (i : Fin 3) : Continuous (fun z : SA3 × V3 =>
        ∑ j : Fin 3, (z.1 : M3) i j*a j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hPentry i j).mul_const (a j))
    have hMovingRow (i : Fin 3) : Continuous (fun z : SA3 × V3 =>
        ∑ j : Fin 3, (z.1 : M3) i j*z.2 j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hPentry i j).mul (hVentry j))
    have hFixed : Continuous (fun z : SA3 × V3 =>
        ∑ i : Fin 3, a i*(∑ j : Fin 3, (z.1 : M3) i j*a j)) :=
      continuous_finsetSum Finset.univ (fun i _ => (hFixedRow i).const_mul (a i))
    have hMoving : Continuous (fun z : SA3 × V3 =>
        ∑ i : Fin 3, z.2 i*(∑ j : Fin 3, (z.1 : M3) i j*z.2 j)) :=
      continuous_finsetSum Finset.univ (fun i _ => (hVentry i).mul (hMovingRow i))
    change Continuous (fun z : SA3 × V3 =>
      (∑ i : Fin 3, a i*(∑ j : Fin 3, (z.1 : M3) i j*a j))+
        ∑ i : Fin 3, z.2 i*(∑ j : Fin 3, (z.1 : M3) i j*z.2 j))
    exact hFixed.add hMoving
  have hOpen : IsOpen (strictSphereCone G ell a) := by
    apply isOpen_iff_mem_nhds.mpr
    intro P hP
    have hEach (v : V3) (hv : v ∈ metricTangentSphere G ell a) :
        ∀ᶠ z : SA3 × V3 in 𝓝 (P,v), 0 < phi z.1 z.2 :=
      hJoint.continuousAt.eventually (lt_mem_nhds (hP v hv))
    exact hCompactSphere.eventually_forall_of_forall_eventually hEach
  have hConeConvex : Convex ℝ (strictSphereCone G ell a) := by
    intro P hP Q hQ t s ht hs hts v hv
    have hLinear : phi (t • P+s • Q) v = t*phi P v+s*phi Q v := by
      dsimp only [phi]
      change dotProduct a ((t • (P : M3)+s • (Q : M3))*ᵥ a)+
        dotProduct v ((t • (P : M3)+s • (Q : M3))*ᵥ v) = _
      simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
        dotProduct_smul,smul_eq_mul]
      ring
    change 0 < phi (t • P+s • Q) v
    rw [hLinear]
    by_cases ht0 : t=0
    · have hs1 : s=1 := by linarith only [hts,ht0]
      simpa only [ht0,hs1,zero_mul,one_mul,zero_add] using hQ v hv
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) (hP v hv))
        (mul_nonneg hs (hQ v hv).le)
  let I : SA3 := 1
  have hIdPositive (v : V3) : 0 < phi I v := by
    have hPa : 0 < dotProduct a a := by
      simpa only [star_trivial,Matrix.one_mulVec] using
        (show (1 : M3).PosDef from Matrix.PosDef.one).dotProduct_mulVec_pos haNe
    have hPv : 0 ≤ dotProduct v v := by
      simpa only [star_trivial,Matrix.one_mulVec] using
        (show (1 : M3).PosSemidef from Matrix.PosSemidef.one).dotProduct_mulVec_nonneg v
    have hI : (I : M3) = (1 : M3) := rfl
    change 0 < dotProduct a ((I : M3) *ᵥ a)+dotProduct v ((I : M3) *ᵥ v)
    rw [hI,Matrix.one_mulVec,Matrix.one_mulVec]
    exact add_pos_of_pos_of_nonneg hPa hPv
  have hConeNonempty : (strictSphereCone G ell a).Nonempty :=
    ⟨I,fun v _ => hIdPositive v⟩
  refine ⟨hClosed,hConvex,hOpen,hConeConvex,hConeNonempty,?_⟩
  intro D
  constructor
  · intro hDual
    by_contra hNotMoment
    obtain ⟨f,b,hDb,hSep⟩ := geometric_hahn_banach_point_closed hConvex hClosed hNotMoment
    have hb : b < 0 := by
      simpa only [map_zero] using hSep 0 hZeroMom
    have hfD : f D < 0 := hDb.trans hb
    have hfMoment (E : SA3) (hE : metricMomentCondition G ell a (E : M3)) : 0 ≤ f E := by
      by_contra h
      have hneg : f E < 0 := lt_of_not_ge h
      let t : ℝ := (b-1)/(f E)
      have ht : 0 < t := div_pos_of_neg_of_neg (by linarith only [hb]) hneg
      have hScaled := hSep (t • E) (hScaleMom t ht.le E hE)
      rw [map_smul] at hScaled
      change b < t*f E at hScaled
      have heq : t*f E = b-1 := div_mul_cancel₀ _ hneg.ne
      rw [heq] at hScaled
      linarith only [hScaled]
    obtain ⟨P,hPair,_⟩ := exists_unique_selfAdjoint_trace_pairing f
    have hTraceD : Matrix.trace ((P : M3)*(D : M3)) < 0 := by
      rw [Matrix.trace_mul_comm,← hPair D]
      exact hfD
    have hGenMoment (v : V3) (hv : v ∈ metricTangentSphere G ell a) :
        metricMomentCondition G ell a
          (Matrix.vecMulVec a a+Matrix.vecMulVec v v) := by
      have hQ : dotProduct ell ((Matrix.vecMulVec a a+Matrix.vecMulVec v v)*ᵥ ell) = 1 := by
        have hRaw : dotProduct ell ((Matrix.vecMulVec a a+Matrix.vecMulVec v v)*ᵥ ell) =
            (dotProduct ell a)^2+(dotProduct ell v)^2 := by
          simp only [dotProduct,Matrix.mulVec,Matrix.add_apply,Matrix.vecMulVec_apply,
            Fin.sum_univ_three]
          ring
        rw [hRaw,ha,hv.1]
        norm_num
      unfold metricMomentCondition
      simp only [hQ,one_smul,add_sub_cancel_left]
      refine ⟨(hRankPSD a).isHermitian.add (hRankPSD v).isHermitian,by norm_num,
        hRankPSD v,?_,?_⟩
      · ext i
        have h : (Matrix.vecMulVec v v *ᵥ ell) i = v i*dotProduct ell v := by
          simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Fin.sum_univ_three]
          ring
        rw [h,hv.1,mul_zero]
        rfl
      · rw [hTraceRank,hv.2,one_mul]
    have hPnonneg (v : V3) (hv : v ∈ metricTangentSphere G ell a) : 0 ≤ phi P v := by
      let E : SA3 := ⟨Matrix.vecMulVec a a+Matrix.vecMulVec v v,
        (hRankPSD a).isHermitian.add (hRankPSD v).isHermitian⟩
      have h := hfMoment E (hGenMoment v hv)
      rw [hPair E,Matrix.trace_mul_comm] at h
      simpa only [E,Matrix.mul_add,Matrix.trace_add,hTraceRank,phi] using h
    let eps : ℝ := (-Matrix.trace ((P : M3)*(D : M3))) /
      (2*(|Matrix.trace (D : M3)|+1))
    have hden : 0 < 2*(|Matrix.trace (D : M3)|+1) := by positivity
    have heps : 0 < eps := div_pos (neg_pos.mpr hTraceD) hden
    have hEpsEq : eps*(2*(|Matrix.trace (D : M3)|+1)) =
        -Matrix.trace ((P : M3)*(D : M3)) := div_mul_cancel₀ _ hden.ne'
    let Q : SA3 := P+eps • I
    have hQin : Q ∈ strictSphereCone G ell a := by
      intro v hv
      have hPairQ : phi Q v = phi P v+eps*phi I v := by
        dsimp only [phi,Q]
        change dotProduct a (((P : M3)+eps • (I : M3))*ᵥ a)+
          dotProduct v (((P : M3)+eps • (I : M3))*ᵥ v) = _
        simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
          dotProduct_smul,smul_eq_mul]
        ring
      change 0 < phi Q v
      rw [hPairQ]
      exact add_pos_of_nonneg_of_pos (hPnonneg v hv) (mul_pos heps (hIdPositive v))
    have hQtrace : Matrix.trace ((Q : M3)*(D : M3)) =
        Matrix.trace ((P : M3)*(D : M3))+eps*Matrix.trace (D : M3) := by
      change Matrix.trace (((P : M3)+eps • (1 : M3))*(D : M3)) = _
      rw [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_add,Matrix.trace_smul]
      rfl
    have hAbs : eps*Matrix.trace (D : M3) ≤ eps*|Matrix.trace (D : M3)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) heps.le
    have hNeg : Matrix.trace ((P : M3)*(D : M3))+eps*Matrix.trace (D : M3) < 0 := by
      have hNonneg := mul_nonneg heps.le (abs_nonneg (Matrix.trace (D : M3)))
      nlinarith only [hEpsEq,hAbs,hNonneg,heps]
    have hContradiction := hDual Q hQin
    rw [hQtrace] at hContradiction
    exact (not_lt_of_ge hContradiction) hNeg
  · intro hMoment P hP
    obtain ⟨w,v,hw,hv,hWeights,hDsum⟩ :=
      (metricMomentCondition_iff_sum_generators G hG ell a ha (D : M3)).mp hMoment
    rw [hDsum]
    simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
      smul_eq_mul]
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (hw k)
    simpa only [Matrix.mul_add,Matrix.trace_add,hTraceRank] using (hP (v k) (hv k)).le

#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.metricTangentSphere
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.strictSphereCone
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.metricMomentCondition
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.exists_unique_selfAdjoint_trace_pairing
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.metricMomentCondition_iff_sum_generators
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.metricMomentCondition_closed_convex_dual

end OAI.AnisotropicCalderon.ProductHessianSeparation
