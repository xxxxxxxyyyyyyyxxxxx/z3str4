/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_ll_pp.h

Abstract:

    AST low level pretty printer.

Author:

    Leonardo de Moura (leonardo) 2006-10-19.

Revision History:

--*/
#pragma once

#include <map>
#include <ostream>
#include <sstream>

#include "ast/ast.h"

using std::string, std::ostringstream;

class AppCounter {
    // count all the following atoms
   public:
    unsigned m_Char = 0;
    unsigned m_str_to_re = 0;
    unsigned m_String = 0;
    unsigned m_str_increment = 0;
    unsigned m_and = 0;
    unsigned m_re_all = 0;
    unsigned m_equals = 0;
    unsigned m_or = 0;
    unsigned m_multiply = 0;
    unsigned m_less_equal = 0;
    unsigned m_plus = 0;
    unsigned m_str_in_re = 0;
    unsigned m_str_replace_re = 0;
    unsigned m_greater_equal = 0;
    unsigned m_str_replace = 0;
    unsigned m_re_multiply = 0;
    unsigned m_str_substr = 0;
    unsigned m_Int = 0;
    unsigned m_re_increment = 0;
    unsigned m_seq_unit = 0;
    unsigned m_re_range = 0;
    unsigned m_str_at = 0;
    unsigned m_not = 0;
    unsigned m_str_len = 0;
    unsigned m_re_allchar = 0;
    unsigned m_str_replace_re_all = 0;
    unsigned m_re_union = 0;
    unsigned m_str_replace_all = 0;
    unsigned m_others = 0;
    unsigned m_num_total = 0;

    string mk_pp_str();
    string mk_total_str();
    string mk_and_or_str();
    int mk_total(){
    return m_Char + m_str_to_re + m_String + m_str_increment + m_and +
                  m_re_all + m_equals + m_or + m_multiply + m_less_equal +
                  m_plus + m_str_in_re + m_str_replace_re + m_greater_equal +
                  m_str_replace + m_re_multiply + m_str_substr + m_Int +
                  m_re_increment + m_seq_unit + m_re_range + m_str_at + m_not +
                  m_str_len + m_re_allchar + m_str_replace_re_all + m_re_union +
                  m_str_replace_all + m_others;
    }
    void mk_pp(std::vector<double>& out){
        out.push_back(m_Char);
        out.push_back(m_str_to_re);
        out.push_back(m_String);
        out.push_back(m_str_increment);
        out.push_back(m_and);
        out.push_back(m_re_all);
        out.push_back(m_equals);
        out.push_back(m_or);
        out.push_back(m_multiply);
        out.push_back(m_less_equal);
        out.push_back(m_plus);
        out.push_back(m_str_in_re);
        out.push_back(m_str_replace_re);
        out.push_back(m_greater_equal);
        out.push_back(m_str_replace);
        out.push_back(m_re_multiply);
        out.push_back(m_str_substr);
        out.push_back(m_Int);
        out.push_back(m_re_increment);
        out.push_back(m_seq_unit);
        out.push_back(m_re_range);
        out.push_back(m_str_at);
        out.push_back(m_not);
        out.push_back(m_str_len);
        out.push_back(m_re_allchar);
        out.push_back(m_str_replace_re_all);
        out.push_back(m_re_union);
        out.push_back(m_str_replace_all);
        out.push_back(m_others);
    }
};
void ast_ll_pp(std::ostream& out, ast_manager& m, ast* n,
               bool only_exprs = true, bool compact = true);
void ast_ll_pp(std::ostream& out, ast_manager& m, ast* n, ast_mark& visited,
               bool only_exprs = true, bool compact = true,
               bool count_each = true);
void ast_def_ll_pp(std::ostream& out, ast_manager& m, ast* n, ast_mark& visited,
                   std::unordered_map<unsigned, unsigned>& ids,
                   bool only_exprs = true, bool compact = true);
void ast_def_ll_pp(std::vector<double>& out, ast_manager& m, ast* n,
                   ast_mark& visited, bool only_exprs, bool compact);
void ast_ll_bounded_pp(std::ostream& out, ast_manager& m, ast* n,
                       unsigned depth);

struct mk_ll_pp {
    ast* m_ast;
    ast_manager& m_manager;
    bool m_only_exprs;
    bool m_compact;
    mk_ll_pp(ast* a, ast_manager& m, bool only_exprs = true,
             bool compact = true)
        : m_ast(a),
          m_manager(m),
          m_only_exprs(only_exprs),
          m_compact(compact) {}
};

inline std::ostream& operator<<(std::ostream& out, mk_ll_pp const& p) {
    ast_ll_pp(out, p.m_manager, p.m_ast, p.m_only_exprs, p.m_compact);
    return out;
}

struct mk_bounded_pp {
    ast* m_ast;
    ast_manager& m_manager;
    unsigned m_depth;
    mk_bounded_pp(ast* a, ast_manager& m, unsigned depth = 3)
        : m_ast(a), m_manager(m), m_depth(depth) {}
};

inline std::ostream& operator<<(std::ostream& out, mk_bounded_pp const& p) {
    ast_ll_bounded_pp(out, p.m_manager, p.m_ast, p.m_depth);
    return out;
}
