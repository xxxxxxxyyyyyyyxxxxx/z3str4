/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_lookahead.cpp

Abstract:

    Lookahead cuber for SMT

Author:

    nbjorner 2019-05-27.

Revision History:

--*/

#include <fcntl.h>
#include <iostream>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <string>
#include <algorithm>
#include <chrono>
#include "solver/parallel_params.hpp"
#include <cmath>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <vector>
using std::cout, std::endl, std::string, std::ostringstream;
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "smt/smt_context.h"
#include "smt/smt_lookahead.h"

namespace smt {

    lookahead::lookahead(context& ctx): 
        ctx(ctx), m(ctx.get_manager()) {}

    struct lookahead::compare {
        context& ctx;
        compare(context& ctx): ctx(ctx) {}

        bool operator()(bool_var v1, bool_var v2) const {
            return ctx.get_activity(v1) > ctx.get_activity(v2);
        }
    };
std::string getLastLine(const std::string &input) {
    size_t lastPos = input.find_last_of('\n');  // 找到最后一个换行符
    if (lastPos == std::string::npos) {
        return "";  // 如果没有换行符，返回空字符串
    }

    size_t secondLastPos =
        input.find_last_of('\n', lastPos - 1);  // 找到倒数第二个换行符
    if (secondLastPos == std::string::npos) {
        return input.substr(0, lastPos);  // 如果只有一行，返回第一行
    }

    return input.substr(secondLastPos + 1,
                        lastPos - secondLastPos -
                            1);  // 返回倒数第一和倒数第二个换行符之间的字符串
}
std::string define2type(const std::string &define) {
    std::string type;
    if (define.find("(=") != std::string::npos) {
        type = "1, 0, 0, 0, 0, ";  // equal
    } else if (define.find("and") != std::string::npos ||
               define.find("or") != std::string::npos ||
               define.find("not") != std::string::npos) {
        type = "0, 1, 0, 0, 0, ";  // bool connective
    } else if (define.find("str.") != std::string::npos) {
        type = "0, 0, 1, 0, 0, ";  // string operation
    } else if (define.find("<") != std::string::npos ||
               define.find("<=") != std::string::npos ||
               define.find(">") != std::string::npos ||
               define.find(">=") != std::string::npos ||
               define.find("+") != std::string::npos ||
               define.find("-") != std::string::npos ||
               define.find("*") != std::string::npos ||
               define.find("/") != std::string::npos) {
        type = "0, 0, 0, 1, 0, ";  // arithmetic operations
    } else {
        type = "0, 0, 0, 0, 1, ";
    }
    return type;
}

bool clause_is_satisfied(clause const &c, context &ctx) {
    for (literal lit : c) {
        switch (ctx.get_assignment(lit)) {
            case l_true:
                return true;
            default:
                break;
        }
    }
    return false;
}
unsigned lookahead::count_satisfied_clauses(context &pctx) {
    unsigned count = 0;
    for (auto &cls : pctx.m_aux_clauses) {
        if (clause_is_satisfied(*cls, pctx)) {
            ++count;
        }
    }
    return count;
}

unsigned count_assigned_bool_vars(context &ctx) {
    unsigned count = 0;
    for (bool_var v = 0; v < ctx.get_num_bool_vars(); ++v) {
        if (ctx.get_assignment(v) != l_undef) {
            ++count;
        }
    }
    return count;
}
    double lookahead::get_score() {
        double score = 0;
        for (clause* cp : ctx.m_aux_clauses) {
            unsigned nf = 0, nu = 0;
            bool is_taut = false;
            for (literal lit : *cp) {
                switch (ctx.get_assignment(lit)) {
                case l_false:
                    if (ctx.get_assign_level(lit) > 0) {
                        ++nf;
                    }
                    break;
                case l_true:
                    is_taut = true;
                    break;
                default:
                    ++nu;
                    break;
                }
            }
            if (!is_taut && nf > 0) {
                score += pow(0.5, static_cast<double>(nu));
            }
        }
        return score;
    }

int find_best_var(std::vector<std::vector<double>> &X, int id, int thread) {
    int fd1, fd2;
    std::string fout = std::to_string(thread) + "-" + std::to_string(id) + ".out";
    std::string fin = std::to_string(thread) + "-" + std::to_string(id) + ".in";
    std::stringstream outputFile;
    outputFile << "[" << endl;
    for (int i = 0; i < X.size(); i++) {
        outputFile << "[";
        for (int j = 0; j < X[i].size(); j++) {
            outputFile << X[i][j];
            if (j != X[i].size() - 1) {
                outputFile << ", ";
            }
        }
        outputFile << "]";
        if (i != X.size() - 1) {
            outputFile << ", ";
        }
        outputFile << endl;
    }
    outputFile << "]" << endl;
    fd1 = open(fout.c_str(), O_WRONLY);
    write(fd1, outputFile.str().c_str(), outputFile.str().size());
    close(fd1);
    fd2 = open(fin.c_str(), O_RDONLY);
    char buffer[128];
    ssize_t bytes_read = read(fd2, buffer, sizeof(buffer));
    buffer[bytes_read] = '\0';
    int choose = std::stoi(buffer);
    close(fd2);
    return choose;
}
    
    expr_ref lookahead::choose(unsigned budget) {
        ctx.pop_to_base_lvl();
        unsigned sz = ctx.m_bool_var2expr.size();
        bool_var best_v = null_bool_var;
        double best_score = -1;
        svector<bool_var> vars;
        for (bool_var v = 0; v < static_cast<bool_var>(sz); ++v) {
            expr* b = ctx.bool_var2expr(v);
            if (b && ctx.get_assignment(v) == l_undef) {
                vars.push_back(v);
            }
        }
        compare comp(ctx);
        std::sort(vars.begin(), vars.end(), comp);
        
        unsigned ns = 0, n = 0;
        for (bool_var v : vars) {
            if (!ctx.bool_var2expr(v)) 
                continue;
            if (!m.inc())
                break;
            literal lit(v, false);
            ctx.propagate();
            if (ctx.inconsistent())
                return expr_ref(m.mk_false(), m);
            ctx.push_scope();
            ctx.assign(lit, b_justification::mk_axiom(), true);
            ctx.propagate();
            bool inconsistent = ctx.inconsistent();
            double score1 = get_score();
            ctx.pop_scope(1);
            if (inconsistent) {
                ctx.assign(~lit, b_justification::mk_axiom(), false);
                ctx.propagate();           
                continue;
            }

            ctx.propagate();
            if (ctx.inconsistent())
                return expr_ref(m.mk_false(), m);
            ctx.push_scope();
            ctx.assign(~lit, b_justification::mk_axiom(), true);
            ctx.propagate();
            inconsistent = ctx.inconsistent();
            double score2 = get_score();
            ctx.pop_scope(1);
            if (inconsistent) {
                ctx.assign(lit, b_justification::mk_axiom(), false);
                ctx.propagate(); 
                continue;
            }
            double score = score1 + score2 + 1024*score1*score2;

            if (score <= 1.1*best_score && best_score <= 1.1*score) {
                if (ctx.get_random_value() % (++n) == 0) {
                    best_score = score;
                    best_v = v;
                }
                ns = 0;
            }
            else if (score > best_score && (ctx.get_random_value() % 2) == 0) {
                n = 0;
                best_score = score;
                best_v = v;
                ns = 0;
            } 
            ++ns;
            if (ns > budget) {
                break;
            }
        }
        expr_ref result(m);
        if (ctx.inconsistent()) {
            result = m.mk_false();
        }
        else if (best_v != null_bool_var) {
            result = ctx.bool_var2expr(best_v);
        }
        else {
            result = m.mk_true();
        }
        return result;
    }

    expr_ref_vector lookahead::choose_rec(unsigned depth) {
        expr_ref_vector trail(m), result(m);
        choose_rec(trail, result, depth, 2000);
        return result;
    }

    expr_ref_vector lookahead::choose_rec(unsigned depth, int id) {
        expr_ref_vector trail(m), result(m);
        choose_rec(trail, result, depth, 2000, id);
        return result;
    }
    void lookahead::choose_rec(expr_ref_vector & trail, expr_ref_vector& result, unsigned depth, unsigned budget) {
            
        expr_ref r = choose(budget);
        if (m.is_true(r)) 
            result.push_back(mk_and(trail));
        else if (m.is_false(r))
            ;
        else {
            auto recurse = [&]() {
                trail.push_back(r);
                if (depth <= 1 || !m.inc()) {
                    result.push_back(mk_and(trail));
                }
                else {
                    ctx.push();
                    ctx.assert_expr(r);
                    ctx.propagate();
                    choose_rec(trail, result, depth-1, 2 * (budget / 3));
                    ctx.pop(1);
                }
                trail.pop_back();
            };
            recurse();
            r = m.mk_not(r);
            recurse();
        }
    }
    void lookahead::choose_rec(expr_ref_vector & trail, expr_ref_vector& result, unsigned depth, unsigned budget, int id) {
            
        expr_ref r = choose(budget, id);
        if (m.is_true(r)) 
            result.push_back(mk_and(trail));
        else if (m.is_false(r))
            ;
        else {
            auto recurse = [&]() {
                trail.push_back(r);
                if (depth <= 1 || !m.inc()) {
                    result.push_back(mk_and(trail));
                }
                else {
                    ctx.push();
                    ctx.assert_expr(r);
                    ctx.propagate();
                    choose_rec(trail, result, depth-1, 2 * (budget / 3));
                    ctx.pop(1);
                }
                trail.pop_back();
            };
            recurse();
            r = m.mk_not(r);
            recurse();
        }
    }
    expr_ref lookahead::choose(unsigned budget, int id){
        verbose_stream() << "start to choose var for therad " << id << "\n";
        ctx.pop_to_base_lvl();
        bool_var best_v = null_bool_var;
        double best_score = -1;
        svector<bool_var> vars;
        unsigned sz = ctx.m_bool_var2expr.size();
        std::unordered_map<unsigned, unsigned> num_occurrences;
        for (bool_var v = 0; v < static_cast<bool_var>(sz); ++v) {
            expr *b = ctx.bool_var2expr(v);
            if (b && ctx.get_assignment(v) == l_undef) {
                vars.push_back(v);
                num_occurrences[v] = 0;
            }
        }
        compare comp(ctx);
        std::sort(vars.begin(), vars.end(), comp);

        unsigned nf = 0, nc = 0, ns = 0, n = 0;
        std::vector<std::vector<double>> X;
        ctx.count_var_in_clause_occurrences(ctx.m_vars);
        ctx.count_degree();
        ctx.count_conflict_occurrences();
        ctx.count_lemma_occurrences();
        std::stringstream temp;
        ctx.display_asserted_formulas(temp, num_occurrences);
        int num_total = 0;
        string str_total;
        while (temp >> str_total) num_total += std::stoi(str_total);
        for (bool_var v : vars) {
            if (budget-- <= 0) break;
            int num_occurrence = num_occurrences[v];
            int gained_lemmas = -2 * ctx.m_lemmas.size();
            int gained_assignments = -2 * count_assigned_bool_vars(ctx);
            int gained_clauses = -2 * count_satisfied_clauses(ctx);
            double score_param = 0;
            literal lit(v, false);
            ctx.propagate();
            if (ctx.inconsistent()) continue;
            ctx.push_scope();
            ctx.assign(lit, b_justification::mk_axiom(), true);
            ctx.propagate();
            gained_lemmas += ctx.m_lemmas.size();
            gained_assignments += count_assigned_bool_vars(ctx);
            gained_clauses += count_satisfied_clauses(ctx);
            score_param += get_score();
            bool inconsistent = ctx.inconsistent();
            ctx.pop_scope(1);
            if (inconsistent) continue;
            ctx.propagate();
            if (ctx.inconsistent()) continue;
            ctx.push_scope();
            ctx.assign(~lit, b_justification::mk_axiom(), true);
            ctx.propagate();
            gained_assignments += count_assigned_bool_vars(ctx);
            gained_clauses += count_satisfied_clauses(ctx);
            gained_lemmas += ctx.m_lemmas.size();
            inconsistent = ctx.inconsistent();
            score_param += get_score();
            ctx.pop_scope(1);
            if (inconsistent) continue;
            std::vector<double> curr_x{
                // static_cast<double>(ctx.get_activity(v)),
                static_cast<double>(ctx.get_assignment_time(v)),
                static_cast<double>(ctx.get_opposite_assignment_count(v)),
                static_cast<double>(ctx.get_var_in_2_clause_occurrences(v)),
                static_cast<double>(ctx.get_var_in_3_clause_occurrences(v)),
                static_cast<double>(ctx.get_var_in_4_clause_occurrences(v)),
                static_cast<double>(ctx.get_conflict_time(v)),
                static_cast<double>(ctx.get_lemma_time(v)),
                ctx.get_average_clause_degree(),
                ctx.get_average_variable_degree(),
                static_cast<double>(ctx.get_lemma_avg_activity()),
                ctx.get_conflict_decision_ration(),
                static_cast<double>(ctx.m_propagation_count),

                static_cast<double>(num_occurrence), 
                static_cast<double>(gained_lemmas), 
                static_cast<double>(gained_assignments),
                static_cast<double>(gained_clauses), score_param,   
                static_cast<double>(num_total),
            };
            ctx.get_pp_visited().reset();
            std::stringstream temp;
            ast_def_ll_pp(curr_x, ctx.m, ctx.bool_var2expr(v), ctx.get_pp_visited(),
                          true, false);
            X.emplace_back(std::move(curr_x));
            ctx.get_pp_visited().reset();
        }
        expr_ref result(m);
        if (X.size() == 0) {
            result = m.mk_true();
            return result;
        }
        parallel_params pp(ctx.m_params);
        int idx = find_best_var(X, id, pp.threads_max());
        verbose_stream() << "end to choose var for therad " << id << "\n";
        result = ctx.bool_var2expr(vars[idx]);
        // mtx.lock();
        // end = std::chrono::system_clock::now();
        // elapsed_seconds += end - start;
        // verbose_stream() << "time: " << elapsed_seconds.count() << "s\n";
        // mtx.unlock();
        return result;
    }
}