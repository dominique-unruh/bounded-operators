    have \<open>\<forall> i. Cauchy (rep_completion (X i))\<close>
      by (metis Quotient3_completion Quotient3_rel_rep normed_space_rel_def)
    hence \<open>\<forall> i. \<exists> L\<in>HFinite. \<forall> N \<in> HNatInfinite. (*f* (rep_completion (X i))) N \<approx> L\<close>
      using limit_point_Cauchy by blast
    hence \<open>\<forall> i. \<exists> L. L\<in>HFinite \<and> (\<forall> N \<in> HNatInfinite. (*f* (rep_completion (X i))) N \<approx> L)\<close>
      by blast
    hence \<open>\<exists> L. \<forall> i. L i \<in> HFinite \<and> (\<forall> N \<in> HNatInfinite. (*f* (rep_completion (X i))) N \<approx> L i)\<close>
      by metis
    then obtain L where \<open>\<forall> i. L i \<in> HFinite\<close>
      and \<open>\<forall> i. \<forall> N \<in> HNatInfinite. (*f* (rep_completion (X i))) N \<approx> L i\<close>
      by blast

    
