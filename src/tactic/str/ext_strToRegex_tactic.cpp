#include "tactic/tactical.h"
#include "tactic/str/ext_strToRegex_tactic.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/var_subst.h"
#include <iostream>
#include <map>
#include <set>

class ext_strToRegex_tactic : public tactic {
    struct imp {
        // typedef generic_model_converter mc;

        ast_manager& m;
        seq_util u;
        arith_util m_autil;
        scoped_ptr<expr_replacer> m_replace;
        ptr_vector<expr> stack;

        // ref<mc> m_mc;
        bool m_produce_models;

        const rational str_to_int_finitization_upper_bound = rational(50);

        imp(ast_manager& _m, params_ref const& p) :
            m(_m),
            u(m),
            m_autil(m) {
            m_replace = mk_default_expr_replacer(m, false);
            updt_params(p);
        }

        void updt_params(params_ref const& p) {

        }

        // Returns a regular expression of the form [0-9]+.
        expr_ref re_one_or_more_digits() {
            //symbol zero("0");
            //symbol nine("9");
            expr_ref re_zero_to_nine(u.re.mk_range(u.str.mk_string("0"), u.str.mk_string("9")), m);
            return expr_ref(u.re.mk_plus(re_zero_to_nine), m);
        }

        // Returns a regular expression of the form (re.++ 0* (re.union 0 1 2 ... upper_bound))
        // Precondition: upper_bound >= 0
        expr_ref finitize_str_to_int(rational upper_bound) {
            if (upper_bound.is_neg()) {
                return expr_ref(m.mk_false(), m);
            }

            expr_ref_vector union_terms(m);
            for (rational i = rational::zero(); i <= upper_bound; i += 1) {
                //symbol i_string(i.to_string().c_str());
                expr_ref i_expr(u.re.mk_to_re(u.str.mk_string(i.to_string().c_str())), m);
                union_terms.push_back(i_expr);
            }

            //symbol zero("0");
            expr_ref re_leading_zeroes(u.re.mk_star(u.re.mk_to_re(u.str.mk_string("0"))), m);

            expr_ref re_union(union_terms.get(0), m);
            if (union_terms.size() > 1) {
                for (unsigned i = 1; i < union_terms.size(); ++i) {
                    re_union = expr_ref(u.re.mk_union(re_union, union_terms.get(i)), m);
                }
            }

            return expr_ref(u.re.mk_concat(re_leading_zeroes, re_union), m);
        }

		/* ####################################################################################
		 * REWRITE functions
		 * ####################################################################################
		 */

        void process_eq(expr* eq, goal_ref const& g, expr_substitution& sub) {
            if (sub.contains(eq)) return;

            expr* lhs;
            expr* rhs;

            m.is_eq(eq, lhs, rhs);

            // Rewrite: (= (str.to_int S) #const) and #const >= 0 --> (str.in_re S (0* ++ #const))
            {
                bool rewrite_applies = false;
                expr* string_subterm = nullptr;
                rational integer_constant;

                if (u.str.is_stoi(lhs, string_subterm)) {
                    if (m_autil.is_numeral(rhs, integer_constant)) {
                        rewrite_applies = true;
                    }
                } else if (u.str.is_stoi(rhs, string_subterm)) {
                    if (m_autil.is_numeral(lhs, integer_constant)) {
                        rewrite_applies = true;
                    }
                }

                if (rewrite_applies) {
                    if (integer_constant.is_nonneg()) {
                        TRACE("ext_strToRegex_tactic", tout << "str.to_int rewrite applies: " << mk_pp(string_subterm, m) << " in 0*" << integer_constant << std::endl;);
                        //symbol integer_constant_string(integer_constant.to_string().c_str());
                        //symbol zero("0");
                        expr_ref regex(u.re.mk_concat(u.re.mk_star(u.re.mk_to_re(u.str.mk_string("0"))), u.re.mk_to_re(u.str.mk_string(integer_constant.to_string().c_str()))), m);
                        expr_ref str_in_regex(u.re.mk_in_re(string_subterm, regex), m);
                        sub.insert(eq, str_in_regex);
                        stack.push_back(str_in_regex);
                        return;
                    }
                }
            }

			// Rewrite 15: x = replace(x, a, b) -> not x in regex .* a .*
			{
				zstring a; zstring b;
                if (u.str.is_replace(rhs)) {
					expr* inthis; expr* replacethis; expr* bythis;
					u.str.is_replace(rhs, inthis, replacethis, bythis);
					if(lhs == inthis && u.str.is_string(replacethis, a) && u.str.is_string(bythis, b) && a != b){
						//std::cout << "Rewrite 15: x = replace(x, a, b) -> not x in regex .* a .* " <<  std::endl;
						expr_ref string_expr(u.str.mk_string(a), m);
						expr_ref string_expr_re(u.re.mk_to_re(string_expr), m);
						sort* re_str_sort = string_expr_re->get_sort();
						expr_ref re_any_string(u.re.mk_full_seq(re_str_sort), m);
						expr_ref regex(u.re.mk_concat(re_any_string, u.re.mk_concat(string_expr_re, re_any_string)), m);
						expr_ref str_in_regex(u.re.mk_in_re(lhs, regex), m);
						expr_ref str_notin_regex(m.mk_not(str_in_regex), m);
						//std::cout << mk_pp(str_notin_regex, m) << std::endl;
						sub.insert(eq, str_notin_regex);
						stack.push_back(str_notin_regex);
						return;
                    }
                }

				if (u.str.is_replace(lhs)) {
					expr* inthis; expr* replacethis; expr* bythis;
					u.str.is_replace(lhs, inthis, replacethis, bythis);
					if(rhs == inthis && u.str.is_string(replacethis, a) && u.str.is_string(bythis, b) && a != b){
						//std::cout << "Rewrite 15: x = replace(x, a, b) -> not x in regex .* a .* " <<  std::endl;
						expr_ref string_expr(u.str.mk_string(a), m);
						expr_ref string_expr_re(u.re.mk_to_re(string_expr), m);
						sort* re_str_sort = string_expr_re->get_sort();
						expr_ref re_any_string(u.re.mk_full_seq(re_str_sort), m);
						expr_ref regex(u.re.mk_concat(re_any_string, u.re.mk_concat(string_expr_re, re_any_string)), m);
						expr_ref str_in_regex(u.re.mk_in_re(rhs, regex), m);
						expr_ref str_notin_regex(m.mk_not(str_in_regex), m);
						//std::cout << mk_pp(str_notin_regex, m) << std::endl;
						sub.insert(eq, str_notin_regex);
						stack.push_back(str_notin_regex);
						return;
                    }
                }
			}

            stack.push_back(lhs);
            stack.push_back(rhs);
        }


        void process_prefix(expr* prefix, goal_ref const& g, expr_substitution& sub) {
            if (sub.contains(prefix)) return;

            expr* needle;
            expr* haystack;
            u.str.is_prefix(prefix, needle, haystack);

           //~ //Replace a Variable that has been marked as a constant before by a constant
            //~ std::map<expr*, expr*>::iterator it;
            //~ it = const_var.find(needle);
            //~ if(it != const_var.end()){
				//~ needle = it->second;
			//~ }

            // Rewrite: (str.prefixof "constant" S) --> (str.in_re S ("constant" ++ .*))
            {
                zstring string_constant;
                if (u.str.is_string(needle, string_constant)) {
                    TRACE("ext_strToRegex_tactic", tout << "str.prefixof rewrite applies: " << mk_pp(haystack, m) << " in " << string_constant << " .*" << std::endl;);
                    expr_ref string_expr(u.str.mk_string(string_constant), m);
                    expr_ref string_expr_re(u.re.mk_to_re(string_expr), m);
                    sort* re_str_sort = string_expr_re->get_sort();
                    expr_ref re_any_string(u.re.mk_full_seq(re_str_sort), m);
                    expr_ref regex(u.re.mk_concat(string_expr_re, re_any_string), m);
                    expr_ref str_in_regex(u.re.mk_in_re(haystack, regex), m);
                    sub.insert(prefix, str_in_regex);
                }
            }

            stack.push_back(needle);
            stack.push_back(haystack);
        }

        void process_suffix(expr* suffix, goal_ref const& g, expr_substitution& sub) {
            if (sub.contains(suffix)) return;

            expr* needle;
            expr* haystack;
            u.str.is_suffix(suffix, needle, haystack);


           //~ //Replace a Variable that has been marked as a constant before by a constant
            //~ std::map<expr*, expr*>::iterator it;
            //~ it = const_var.find(needle);
            //~ if(it != const_var.end()){
				//~ needle = it->second;
			//~ }

            // Rewrite: (str.suffixof "constant" S) --> (str.in_re S (.* ++ "constant"))
            {
                zstring string_constant;
                if (u.str.is_string(needle, string_constant)) {
                    TRACE("ext_strToRegex_tactic", tout << "str.suffixof rewrite applies: " << mk_pp(haystack, m) << " in .* " << string_constant << std::endl;);
                    expr_ref string_expr(u.str.mk_string(string_constant), m);
                    expr_ref string_expr_re(u.re.mk_to_re(string_expr), m);
                    sort* re_str_sort = string_expr_re->get_sort();
                    expr_ref re_any_string(u.re.mk_full_seq(re_str_sort), m);
                    expr_ref regex(u.re.mk_concat(re_any_string, string_expr_re), m);
                    expr_ref str_in_regex(u.re.mk_in_re(haystack, regex), m);
                    sub.insert(suffix, str_in_regex);
                }
            }

            stack.push_back(needle);
            stack.push_back(haystack);
        }

        void process_contains(expr* contains, goal_ref const& g, expr_substitution& sub) {
            if (sub.contains(contains)) return;

            expr * needle;
            expr * haystack;
            u.str.is_contains(contains, haystack, needle);


            //~ //Replace a Variable that has been marked as a constant before in rewrite-preprocessing
            //~ std::map<expr*, expr*>::iterator it;
            //~ it = const_var.find(needle);
            //~ if(it != const_var.end()){
				//~ needle = it->second;
			//~ }

            // Rewrite: (str.contains X "const") -> (str.in_re X (re.++ .* "const" .*))
            {
                zstring string_constant;
                if (u.str.is_string(needle, string_constant)) {
                    //TRACE("ext_strToRegex_tactic", tout << "str.contains rewrite applies: " << mk_pp(haystack, m) << " in .* \"" << string_constant << "\" .*" << std::endl;);
                    //std::cout << "Rewrite: (str.contains X const) -> (str.in_re X (re.++ .* const .*))" << std::endl;
                    expr_ref string_expr(u.str.mk_string(string_constant), m);
                    expr_ref string_expr_re(u.re.mk_to_re(string_expr), m);
                    sort* re_str_sort = string_expr_re->get_sort();
                    expr_ref re_any_string(u.re.mk_full_seq(re_str_sort), m);
                    expr_ref regex(u.re.mk_concat(re_any_string, u.re.mk_concat(string_expr_re, re_any_string)), m);
                    expr_ref str_in_regex(u.re.mk_in_re(haystack, regex), m);
                    sub.insert(contains, str_in_regex);

					//Put this here in case smth is different in other rewrites (Stefan)
					stack.push_back(str_in_regex);
					return;
                }
            }

			stack.push_back(needle);
			stack.push_back(haystack);

        }

		/* ####################################################################################
		 * TRAVERSING formula
		 * ####################################################################################
		 */
        void operator()(goal_ref const& g, goal_ref_buffer& result) {
            SASSERT(g->is_well_formed());
            tactic_report report("ext_str", *g);
            fail_if_proof_generation("ext_str", g);
            SASSERT(g->is_well_formed());
            // m_produce_models = g->models_enabled();
            // if (m_produce_models) {
            //     m_mc = alloc(generic_model_converter, m, "ext_str");
            // } else {
            //     m_mc = nullptr;
            // }

            SASSERT(g->is_well_formed());

            result.reset();

            TRACE("ext_strToRegex_tactic", tout << "BEFORE:" << std::endl; g->display(tout););

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

			unsigned size = g->size();
            expr_substitution sub(m);
            //std::cout << size << std::endl;
            for (unsigned idx = 0; idx < size; ++idx) {
                if (g->inconsistent()) break;
                expr* curr = g->form(idx);
				//std::cout << mk_pp(curr, m) << std::endl;
                if (is_app(curr)) {
                    stack.reset();
                    stack.push_back(curr);

                    while (!stack.empty()) {
                        curr = stack.back();
                        stack.pop_back();

                        if (!is_app(curr)) continue;

                        TRACE("ext_strToRegex_tactic", tout << "curr: " << mk_pp(curr, m) << std::endl;);

                        if (m.is_eq(curr)) {
                            process_eq(curr, g, sub);
                        } else if (u.str.is_prefix(curr)) {
                            process_prefix(curr, g, sub);
                        } else if (u.str.is_suffix(curr)) {
                            process_suffix(curr, g, sub);
                        } else if (u.str.is_contains(curr)) {
                            process_contains(curr, g, sub);
						} else {
                            app * a = to_app(curr);
                            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                                expr * arg = a->get_arg(i);
                                stack.push_back(arg);
                            }
                        }
                    }
                }
            }

            m_replace->set_substitution(&sub);

            for (unsigned i = 0; i < g->size(); ++i) {
                expr_ref new_curr(m);
                proof_ref new_pr(m);
                (*m_replace)(g->form(i), new_curr, new_pr);
                if (m.proofs_enabled() && !new_pr) {
                    new_pr = m.mk_rewrite(g->form(i), new_curr);
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                g->update(i, new_curr, new_pr, g->dep(i));
            }

            g->inc_depth();
            result.push_back(g.get());
            SASSERT(g->is_well_formed());
            TRACE("ext_strToRegex_tactic", tout << "AFTER: " << std::endl; g->display(tout););
            // if (g->mc()) g->mc()->display(tout); tout << std::endl;);
        }
    };

    imp* m_imp;
    params_ref m_params;

public:
    ext_strToRegex_tactic(ast_manager& m, params_ref const& p) :
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(ext_strToRegex_tactic, m, m_params);
    }

    ~ext_strToRegex_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const& p) override {
	//m_params = p;
        m_params.append(p);
	m_imp->updt_params(p);
    }

    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        try {
            (*m_imp)(in, result);
        }
        catch (rewriter_exception& ex) {
            throw tactic_exception(ex.msg());
        }
    }

    void cleanup() override {
        imp* d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);
        dealloc(d);
    }
    char const* name() const override { return "z3str3_tactic"; }
};

tactic * mk_ext_strToRegex_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ext_strToRegex_tactic, m, p));
}
