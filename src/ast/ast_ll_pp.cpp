/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_ll_pp.cpp

Abstract:
 
    AST low level pretty printer.
    
Author:

    Leonardo de Moura (leonardo) 2006-10-19.

Revision History:

--*/

#include "ast/ast_ll_pp.h"
#include "ast/for_each_ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"


#include <iostream>
#include <map>
#include <sstream>
#include <vector>
using std::cout, std::endl, std::string;
// #define AST_LL_PP_SHOW_FAMILY_NAME
// calc the total number of atoms
std::string AppCounter::mk_total_str() {
    if (m_num_total) return std::to_string(m_num_total);
    m_num_total = m_Char + m_str_to_re + m_String + m_str_increment + m_and +
                  m_re_all + m_equals + m_or + m_multiply + m_less_equal +
                  m_plus + m_str_in_re + m_str_replace_re + m_greater_equal +
                  m_str_replace + m_re_multiply + m_str_substr + m_Int +
                  m_re_increment + m_seq_unit + m_re_range + m_str_at + m_not +
                  m_str_len + m_re_allchar + m_str_replace_re_all + m_re_union +
                  m_str_replace_all + m_others;
    return std::to_string(m_num_total);
}
string AppCounter::mk_and_or_str() {
    return std::to_string(m_and) + " " + std::to_string(m_or);
}
// return a string of all the fields separated by comma, except the last one
std::string AppCounter::mk_pp_str() {
    return std::to_string(m_Char) + ", " + std::to_string(m_str_to_re) + ", " +
           std::to_string(m_String) + ", " + std::to_string(m_str_increment) +
           ", " + std::to_string(m_and) + ", " + std::to_string(m_re_all) +
           ", " + std::to_string(m_equals) + ", " + std::to_string(m_or) +
           ", " + std::to_string(m_multiply) + ", " +
           std::to_string(m_less_equal) + ", " + std::to_string(m_plus) + ", " +
           std::to_string(m_str_in_re) + ", " +
           std::to_string(m_str_replace_re) + ", " +
           std::to_string(m_greater_equal) + ", " +
           std::to_string(m_str_replace) + ", " +
           std::to_string(m_re_multiply) + ", " + std::to_string(m_str_substr) +
           ", " + std::to_string(m_Int) + ", " +
           std::to_string(m_re_increment) + ", " + std::to_string(m_seq_unit) +
           ", " + std::to_string(m_re_range) + ", " + std::to_string(m_str_at) +
           ", " + std::to_string(m_not) + ", " + std::to_string(m_str_len) +
           ", " + std::to_string(m_re_allchar) + ", " +
           std::to_string(m_str_replace_re_all) + ", " +
           std::to_string(m_re_union) + ", " +
           std::to_string(m_str_replace_all) + ", " + std::to_string(m_others);
}

std::string bool_var2one_hot(std::string type) {
    std::vector<string> types = {
        "or",
        "chat.bit",
        "<=",
        "=",
        "seq.length_limit"
        ">=",
        "seq.max_unfolding",
        "aut.accept",
        "str.in_re",
    };
    std::vector<int> oneHotVector(types.size() + 1, 0);
    bool others = true;
    for (int i = 0; i < types.size(); i++) {
        if (type == types[i]) {
            oneHotVector[i] = 1;
            others = false;
            break;
        }
    }
    if (!others) oneHotVector[types.size()] = 1;
    std::ostringstream oss;
    for (size_t i = 0; i < oneHotVector.size(); ++i) {
        oss << oneHotVector[i];
        if (i < oneHotVector.size() - 1) {
            oss << ", ";
        }
    }
    return oss.str();
}
class ll_printer {
    std::ostream& m_out;
    ast_manager& m_manager;
    ast* m_root;
    bool m_only_exprs;
    bool m_compact;
    arith_util m_autil;
    datatype_util m_dt;
    bool count_each = true;

    void display_def_header(ast * n) {
        if (n != m_root) {
            m_out << "#" << n->get_id() << " := ";
        }
    }

    void display_child_ref(ast * n) {
        m_out << "#" << n->get_id();
    }

    void display_name(func_decl * decl) {
        m_out << decl->get_name();
    }

    bool process_numeral(expr * n) {
        rational val;
        bool is_int;
        if (m_autil.is_numeral(n, val, is_int)) {
            m_out << val;
            if (!is_int && val.is_int()) m_out << ".0";
            return true;
        }
        return false;
    }

    void display_sort(sort * s) {
        m_out << s->get_name();
        display_params(s);
    }
        
    void display_child(ast * n) {
        switch (n->get_kind()) {
        case AST_SORT:
            display_sort(to_sort(n));
            break;
        case AST_APP:
            if (process_numeral(to_expr(n))) {
                // skip
            }
            else if (to_app(n)->get_num_args() == 0) {
                display_name(to_app(n)->get_decl());
                display_params(to_app(n)->get_decl());
            }
            else {
                display_child_ref(n);
            }
            break;
        case AST_FUNC_DECL:
            m_out << to_func_decl(n)->get_name();
            break;
        default:
            display_child_ref(n);
        }

    }

    template<typename T>
    void display_children(unsigned num_children, T * const * children) {
        for (unsigned i = 0; i < num_children; i++) {
            if (i > 0) {
                m_out << " ";
            }
            display_child(children[i]);
        }
    }

    void display_params(decl * d) {
        unsigned n = d->get_num_parameters();
        parameter const* p = d->get_parameters();
        if (n > 0 && p[0].is_symbol() && d->get_name() == p[0].get_symbol()) {
            n--;
            p++;
        } 

        if (n > 0 && !d->private_parameters()) {
            m_out << "[";
            for (unsigned i = 0; i < n; i ++) {
                if (p[i].is_ast()) {
                    display_child(p[i].get_ast());
                }
                else {
                    m_out << p[i];
                }
                m_out << (i < n-1 ? ":" : "");
            }
            m_out << "]";
        }
        else if (is_func_decl(d) && m_dt.is_is(to_func_decl(d))) {
            func_decl* fd = m_dt.get_recognizer_constructor(to_func_decl(d));
            m_out << " " << fd->get_name();
        }
    }

public:
    AppCounter m_app_counter;
    std::unordered_map<unsigned, unsigned>& m_ids;
    ll_printer(std::ostream& out, ast_manager& m, ast* n, bool only_exprs,
               bool compact, bool count_each,
               std::unordered_map<unsigned, unsigned>& ids)
        : m_out(out),
          m_manager(m),
          m_root(n),
          m_only_exprs(only_exprs),
          m_compact(compact),
          m_autil(m),
          count_each(count_each),
          m_dt(m),
          m_ids(ids) {}

    void pp(ast* n) {
        ast_mark visited;
        pp(n, visited);
    }

    void pp(ast* n, ast_mark& visited) {
        if (is_sort(n)) {
            display_sort(to_sort(n));
        }
        else {
            for_each_ast(*this, visited, n, true);
        }
    }

    void operator()(sort* n) {
    }

    void operator()(func_decl * n) {
    }
        
    void operator()(var * n) {
    }

    void operator()(app * n) {
        if (!count_each) {
            if (m_ids.find(n->get_id()) != m_ids.end()) {
                m_ids[n->get_id()]++;
            }
            m_app_counter.m_num_total++;
        } else {
            string name = n->get_name().bare_str();
            if (name == "str.++") {
                m_app_counter.m_str_increment++;
            } else if (name == "seq.unit") {
                m_app_counter.m_seq_unit++;
            } else if (name == "Char") {
                m_app_counter.m_Char++;
            } else if (name == "=") {
                m_app_counter.m_equals++;
            } else if (name == "and") {
                m_app_counter.m_and++;
            } else if (name == "or") {
                m_app_counter.m_or++;
            } else if (name == "str.len") {
                m_app_counter.m_str_len++;
            } else if (name == "Int") {
                m_app_counter.m_Int++;
            } else if (name == "str.to_re") {
                m_app_counter.m_str_to_re++;
            } else if (name == "String") {
                m_app_counter.m_String++;
            } else if (name == "re.all") {
                m_app_counter.m_re_all++;
            } else if (name == "*") {
                m_app_counter.m_multiply++;
            } else if (name == "<=") {
                m_app_counter.m_less_equal++;
            } else if (name == "+") {
                m_app_counter.m_plus++;
            } else if (name == "str.in_re") {
                m_app_counter.m_str_in_re++;
            } else if (name == "str.replace_re") {
                m_app_counter.m_str_replace_re++;
            } else if (name == ">=") {
                m_app_counter.m_greater_equal++;
            } else if (name == "str.replace") {
                m_app_counter.m_str_replace++;
            } else if (name == "re.*") {
                m_app_counter.m_re_multiply++;
            } else if (name == "str.substr") {
                m_app_counter.m_str_substr++;
            } else if (name == "re.++") {
                m_app_counter.m_re_increment++;
            } else if (name == "re.range") {
                m_app_counter.m_re_range++;
            } else if (name == "str.at") {
                m_app_counter.m_str_at++;
            } else if (name == "not") {
                m_app_counter.m_not++;
            } else if (name == "re.allchar") {
                m_app_counter.m_re_allchar++;
            } else if (name == "str.replace_re_all") {
                m_app_counter.m_str_replace_re_all++;
            } else if (name == "re.union") {
                m_app_counter.m_re_union++;
            } else if (name == "str.replace_all") {
                m_app_counter.m_str_replace_all++;
            } else {
                m_app_counter.m_others++;
            }
        }
    }

    void display_quantifier_header(quantifier* n) {
        m_out << "(" << (n->get_kind() == forall_k ? "forall" : (n->get_kind() == exists_k ? "exists" : "lambda")) << " ";
        unsigned num_decls = n->get_num_decls();
        m_out << "(vars ";
        for (unsigned i = 0; i < num_decls; i++) {
            if (i > 0) {
                m_out << " ";
            }
            m_out << "(" << n->get_decl_name(i) << " ";
            display_sort(n->get_decl_sort(i));
            m_out << ")";
        }
        m_out << ") ";
        if (n->get_num_patterns() > 0) {
            m_out << "(:pat ";
            display_children(n->get_num_patterns(), n->get_patterns());
            m_out << ") ";
        }
        if (n->get_num_no_patterns() > 0) {
            m_out << "(:nopat ";
            display_children(n->get_num_no_patterns(), n->get_no_patterns());
            m_out << ") ";
        }

  }

    void operator()(quantifier * n) {
    }

    void display(expr * n, unsigned depth) {
        if (is_var(n)) {
            m_out << "(:var " << to_var(n)->get_idx() << ")";
            return;
        }
        if (is_quantifier(n)) {
            display_quantifier_header(to_quantifier(n));
            display(to_quantifier(n)->get_expr(), depth - 1);
            m_out << ")";
            return;
        }

        if (!is_app(n) || depth == 0 || to_app(n)->get_num_args() == 0) {
            display_child(n);
            return;
        }
        unsigned num_args = to_app(n)->get_num_args();
        
        if (num_args > 0) 
            m_out << "(";
        display_name(to_app(n)->get_decl());
        display_params(to_app(n)->get_decl());
        for (unsigned i = 0; i < num_args && i < 16; i++) {
            m_out << " ";
            display(to_app(n)->get_arg(i), depth-1);
        }
        if (num_args >= 16) 
            m_out << " ...";
        if (num_args > 0)
            m_out << ")";
    }

    void display_bounded(ast * n, unsigned depth) {
        if (!n)
            m_out << "null";    
        else if (is_expr(n)) 
            display(to_expr(n), depth);               
        else 
            m_out << "#" << n->get_id();        
    }
};

void ast_ll_pp(std::ostream& out, ast_manager& m, ast* n, bool only_exprs,
               bool compact) {
    // ll_printer p(out, m, n, only_exprs, compact);
    // p.pp(n);
}

void ast_ll_pp(std::ostream& out, ast_manager& m, ast* n, ast_mark& visited,
               bool only_exprs, bool compact) {
    // ll_printer p(out, m, n, only_exprs, compact);
    // p.pp(n, visited);
}
// Function to generate a one-hot encoded vector as a comma-separated string
void oneHotEncode(const std::string& input, std::vector<double>& out) {
    // Map of types to their corresponding one-hot index (ignoring the numbers)
    std::vector<std::string> types = {"str.++",     "seq.unit",
                                      "Char",       "=",
                                      "or",         "and",
                                      "str.len",    "Int",
                                      "String",     "*",
                                      "<=",         "+",
                                      "str.in_re",  "str.replace_re",
                                      ">=",         "str.replace",
                                      "re.*",       "str.substr",
                                      "str.to_re",  "re.++",
                                      "re.range",   "str.at",
                                      "not",        "re.all",
                                      "re.allchar", "str.replace_re_all",
                                      "re.union",   "str.replace_all"};

    auto it = std::find(types.begin(), types.end(), input);
    if (it != types.end()) {
        for (int i = 0; i < types.size() + 1; i++) {
            if (i != std::distance(types.begin(), it))
                out.push_back(0);
            else
                out.push_back(1);
        }
   } else {
        for (int i = 0; i < types.size(); i++) out.push_back(0);
        out.push_back(1);
    }
}
void ast_def_ll_pp(std::ostream& out, ast_manager& m, ast* n, ast_mark& visited,
                   std::unordered_map<unsigned, unsigned>& ids, bool only_exprs,
                   bool compact) {
    ll_printer p(out, m, nullptr, only_exprs, compact, false, ids);
    visited.reset();
    p.pp(n, visited);
    out << p.m_app_counter.mk_total_str() << endl;
}
void ast_def_ll_pp(std::vector<double>& out, ast_manager& m, ast* n,
                   ast_mark& visited, bool only_exprs, bool compact) {
    std::unordered_map<unsigned, unsigned> temp;
    std::ostringstream temp2;
    ll_printer p(temp2, m, nullptr, only_exprs, compact, true, temp);
    visited.reset();
    p.pp(n, visited);
    out.push_back(p.m_app_counter.mk_total());
    oneHotEncode(to_app(n)->get_name().bare_str(), out);
    p.m_app_counter.mk_pp(out);
}

void ast_ll_bounded_pp(std::ostream& out, ast_manager& m, ast* n,
                       unsigned depth) {
    // ll_printer p(out, m, nullptr, false, true);
    // p.display_bounded(n, depth);
}
