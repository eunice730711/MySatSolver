//
//  main.cpp
//  milestone1
//
//  Created by Emily on 2016/11/6.
//  Copyright © 2016年 Emily. All rights reserved.
//
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
#include <map>
#include <cmath>
#include <queue>
#include <stack>
#include <set>
#include <deque>
#include <fstream>
#include <time.h>
#include "parser.h"
using namespace std;
vector<vector<int> > clauses;
int maxVarIndex;

struct variable
{
    int idx,val;
    int preval;
    int level,order,implyc;
};
vector<vector<int> > pw,nw;
vector<pair<int,int> > watch; // watching literal in clauses
vector<variable> vars,assign; // var status ( for 2 literal watching )
vector<int> unit; //unit clauses
vector<double> act_score;
set<int> satv,assignv; // record ALL SAT clauses and ALL assigned var
bool checkbigger = false;

void initial_watch()
{
    for(int i=0;i<clauses.size();i++) // watch
    {
        if(clauses[i].size()>=2) watch.push_back(make_pair(clauses[i][0],clauses[i][1]));
        else if(clauses[i].size()==1){  // clause only have one literal
            watch.push_back(make_pair(clauses[i][0],0)); //can delete???
            unit.push_back(clauses[i][0]); //unit clauses
        }
    }
}
void new_watch(vector<int> clause)
{
    if(clause.size()==0) return;
    int box1=0,box2=0;
    pair<int,int> tmpp(0,0);
    for(int i=0;i<clause.size();i++)
    {
          if(vars[abs(clause[i])].val == -1)
          {
                if(box1==0)
                {
                    tmpp.first = clause[i];
                    box1=1;
                }
                else if(box2==0)
                {
                    tmpp.second = clause[i];
                    box2=1;
                }
                else if(box1==2)
                {
                    tmpp.first = clause[i];
                    box1=1;
                }
                else if(box2==2)
                {
                    tmpp.second = clause[i];
                    box2=1;
                }
                continue;
            }
            else
            {
                if(box1==0)
                {
                    tmpp.first = clause[i];
                    box1=2;
                }
                else if(box2==0)
                {
                    tmpp.second = clause[i];
                    box2=2;
                }
                else if(box1==2 && vars[abs(clause[i])].level > vars[abs(tmpp.first)].level)
                {
                    tmpp.first = clause[i];
                    box1=2;
                }
                else if(box2==2 && vars[abs(clause[i])].level > vars[abs(tmpp.second)].level)
                {
                    tmpp.second = clause[i];
                    box2=2;
                }
            }
    }

    watch.push_back(tmpp);
    clauses.push_back(clause);
    int idx = clauses.size()-1;
    if(tmpp.first !=0)
    {
        if(tmpp.first < 0) nw[abs(tmpp.first)].push_back(idx);
        else if(tmpp.first >0) pw[tmpp.first].push_back(idx);
    }
    if(tmpp.second !=0)
    {
        if(tmpp.second <0) nw[abs(tmpp.second)].push_back(idx);
        else if(tmpp.second >0) pw[tmpp.second].push_back(idx);
    }
}
void initial_var()
{
    // initial var & pw & nw
    // fill in zero index (we don't need it!)
    variable zero;
    vars.push_back(zero);
    vector<int> zeropw,zeronw;
    pw.push_back(zeropw),nw.push_back(zeronw);
    
    for(int i=1;i<=maxVarIndex;i++) // vars
    {
        variable tmpv;
        vector<int> tmppw,tmpnw;
        
        tmpv.idx = i;
        tmpv.level = -1; //unassign level
        tmpv.val = -1; //unassign value
        tmpv.preval = -1; 
        tmpv.order = -1;
        for(int j=0;j<watch.size();j++)
        {
            if(watch[j].first == i || watch[j].second == i) tmppw.push_back(j);
            if(watch[j].first == -i || watch[j].second == -i) tmpnw.push_back(j);
        }
        pw.push_back(tmppw);
        nw.push_back(tmpnw);
        vars.push_back(tmpv);
    }
}
void set_UNIT(deque<int> &tmpassign)
{
    for(int i=0;i<unit.size();i++)
    {
        int v = unit[i];
        if(v>0) vars[v].val = 1, vars[v].level = 0; // var = 1@0
        else if(v<0) vars[-v].val = 0, vars[-v].level = 0; // var = 0@0
        assign.push_back(vars[abs(v)]); //global assigned variables
        tmpassign.push_front(abs(v)); // assigned in the first round (became unit in the very beginning)
    }
}

int BCPLiteralWatching(int lev, deque<int> &tmpassign) // if true:return -1 ; if false:return conflict clauses
{
    int ord = 2;
    map<int,bool> check;
    while(!tmpassign.empty()) // check whether new imply varibles can imply new variables
    {
        int tmpi = tmpassign.front();
        //cout << "out: tmpi: " << tmpi << endl;
        // cout << "tmpi.preval: " << tmpi << ' ' << vars[abs(tmpi)].preval << endl;
        // cout << "tmpi.val: " << tmpi << ' ' << vars[abs(tmpi)].val << endl;
        assignv.insert(tmpi);
        tmpassign.pop_front();
        
        if(vars[abs(tmpi)].val == -1 && vars[abs(tmpi)].preval != -1)
        {
            vars[abs(tmpi)].val = vars[tmpi].preval;
            vars[abs(tmpi)].level = lev;
            vars[abs(tmpi)].order = ord;
            vars[abs(tmpi)].preval = -1;
            ord+=1;
            //assignv.insert(tmpi);
        }
        if(check[abs(tmpi)]) continue;
        check[abs(tmpi)]=true;
        //cout << "a: tmpi.val: " << tmpi << ' ' << vars[tmpi].val << endl;
        
        if(vars[tmpi].val == 1) // if val == 1 : check nw clauses
        {
            vector<int> deletions;
            //for(int i=0;i<pw[tmpi].size();i++) satv.insert(pw[tmpi][i]); //clauses became SAT
            for(int i=0;i<nw[tmpi].size();i++) // check every clauses stored in nw
            {
                vector<int> c = clauses[nw[tmpi][i]]; // c is the clause which we are deal with now!
                bool next = false, issat = false, first = false;
                if(tmpi == abs(watch[nw[tmpi][i]].first)) first = true; // var appear at first watch literal
                for(int j=0;j<c.size();j++)
                {
                    //check if not-assigned, not-watched
                    int tmpidx = c[j];
                    //check if this clause allready SAT (still have to do something...)
                    if((tmpidx > 0 && vars[abs(tmpidx)].val == 1) || (tmpidx < 0 && vars[abs(tmpidx)].val == 0)) issat = true;
                    //check if not-assigned, not-watched
                    if(vars[abs(tmpidx)].val == -1 && tmpidx!=watch[nw[tmpi][i]].first && tmpidx!=watch[nw[tmpi][i]].second)
                    {
                        if(first) watch[nw[tmpi][i]].first = tmpidx;
                        else watch[nw[tmpi][i]].second = tmpidx;
                        
                        //reset pw & nw
                        if(tmpidx >0) pw[tmpidx].push_back(nw[tmpi][i]); //reset pw
                        else nw[-tmpidx].push_back(nw[tmpi][i]); // reset nw
                        
                        //record deletions' index
                        deletions.push_back(nw[tmpi][i]);
                        next = true;
                        break;
                    }
                }
                if(next) continue; //next watching literal is setted
                int vind =0; //another watch literal
                if(first) vind = watch[nw[tmpi][i]].second;
                else vind = watch[nw[tmpi][i]].first;
                
                if((vind > 0 && vars[abs(vind)].val == 1) || ((vind < 0 && vars[abs(vind)].val == 0)) || issat)
                {
                    // cout << "test2" << endl;
                    // another watch literal already assign to true
                    satv.insert(nw[tmpi][i]);
                }
                else if(vars[abs(vind)].val == -1)
                {
                    // cout << "test3" << endl;
                    // another watch literal has NOT been assigned
                    if(vind >0)
                    {
                        vars[abs(vind)].implyc = nw[tmpi][i];
                        vars[abs(vind)].preval = 1;
                        // cout << abs(vind) << ' ' << '1' << endl;
                    }
                    else
                    {
                        vars[abs(vind)].implyc = nw[tmpi][i];
                        vars[abs(vind)].preval = 0;
                        //cout << abs(vind) << ' ' << '0' << endl;
                    }
                    
                    vars[abs(vind)].implyc = nw[tmpi][i];
                    //assignv.insert(abs(vind));
                    tmpassign.push_back(abs(vind)); //new imply variable
                }
                else if( ((vind > 0 && vars[abs(vind)].val == 0) || (vind < 0 && vars[abs(vind)].val == 1)) && !issat) // conflict
                {
                	//cout << "2nw:"<< nw[tmpi][i] << endl;
                	int clauseno = nw[tmpi][i];
                    // another watch literal already assign to false
                    for(int j=0;j<deletions.size();j++)
                    {
                        nw[tmpi].erase(remove(nw[tmpi].begin(),nw[tmpi].end(),deletions[j]),nw[tmpi].end());
                    }
                    // RETURN CONFLICT CLAUSE
                    return clauseno;
                }
            }
            //ERASE BY VALUE
            for(int j=0;j<deletions.size();j++)
            {
                nw[tmpi].erase(remove(nw[tmpi].begin(),nw[tmpi].end(),deletions[j]),nw[tmpi].end());
            }
        }
        else if(vars[tmpi].val == 0)
        {
            //cout << "b: tmpi.val: " << tmpi << ' ' << vars[tmpi].val << endl;
            vector<int> deletions;
            //cout << "tmpi: " << tmpi << endl;
            //cout << nw[tmpi].size() << ' ' << cout << pw[tmpi].size() << endl;
            //for(int i=0;i<nw[tmpi].size();i++) satv.insert(nw[tmpi][i]);
            for(int i=0;i<pw[tmpi].size();i++) // check every clauses stored in pw
            {
                vector<int> c = clauses[pw[tmpi][i]];
                bool next = false, issat = false, first = false;
                if(tmpi == abs(watch[pw[tmpi][i]].first)) first = true; // var appear at first watch literal
                
                // CHECK THE THIS CLAUSE
                for(int j=0;j<c.size();j++)
                {
                    int tmpidx = c[j];
                    if((c[j] > 0 && vars[abs(tmpidx)].val == 1) || (c[j] < 0 && vars[abs(tmpidx)].val == 0)) issat = true;
                    if(vars[abs(tmpidx)].val == -1 && tmpidx!=watch[pw[tmpi][i]].first && tmpidx!=watch[pw[tmpi][i]].second)
                    {
                        if(first) watch[pw[tmpi][i]].first = tmpidx;
                        else watch[pw[tmpi][i]].second = tmpidx;
                        
                        // SET PW OR NW
                        if(tmpidx >0) pw[tmpidx].push_back(pw[tmpi][i]); //reset pw
                        else nw[-tmpidx].push_back(pw[tmpi][i]); // reset nw
                        // RECORD DELETIONS' INDEX
                        deletions.push_back(pw[tmpi][i]);
                        next = true;
                        break;
                    }
                    
                }
                if(next) continue;//next watching literal is setted
                //cout << "d: tmpi.val: " << tmpi << ' ' << vars[tmpi].val << endl;
                int vind =0; //another watch literal
                if(first) vind = watch[pw[tmpi][i]].second;
                else vind = watch[pw[tmpi][i]].first;
                if((vind > 0 && vars[abs(vind)].val == 1) || ((vind < 0 && vars[abs(vind)].val == 0)) || issat)
                {
                    satv.insert(pw[tmpi][i]);
                }
                else if(vars[abs(vind)].val == -1)
                {
                    if(vind >0)
                    {
                        vars[abs(vind)].implyc = pw[tmpi][i];
                        vars[abs(vind)].preval = 1;
                    }
                    else
                    {
                        vars[abs(vind)].implyc = pw[tmpi][i];
                        vars[abs(vind)].preval = 0;
                    }
                    
                    vars[abs(vind)].implyc = pw[tmpi][i];
                    tmpassign.push_back(abs(vind));
                }
                else if( ((vind > 0 && vars[abs(vind)].val == 0) || (vind < 0 && vars[abs(vind)].val == 1)) && !issat) // conflict
                {
                	int clauseno = pw[tmpi][i];
                    for(int j=0;j<deletions.size();j++)
                    {
                        pw[tmpi].erase(remove(pw[tmpi].begin(),pw[tmpi].end(),deletions[j]),pw[tmpi].end());
                    }
                    // GET CONFLICT CLAUSE
                    return clauseno;
                }
            }
            for(int j=0;j<deletions.size();j++)
            {
                pw[tmpi].erase(remove(pw[tmpi].begin(),pw[tmpi].end(),deletions[j]),pw[tmpi].end());
            }
        }
        
    }
    return -1;
}

void heuristic(priority_queue<pair<double,int> > &scores, vector<int> newc)
{
    //cout << "heuristic decide: " << decide.size() << endl;
    priority_queue<pair<double,int> > newscores;
    double constant=0.95;
    set<int> span;
    map<int,bool> add;
    vector<int>::iterator it;
    for(int i=0;i<newc.size();i++)
    {
        //vars[abs(newc[i])].act_score += 1;
        act_score[abs(newc[i])] +=1;
        add[abs(newc[i])]=true;
        span.insert(vars[abs(newc[i])].level);
    }
    for(int i=1;i<=maxVarIndex;i++)
    {
        if(add[i] == false) (act_score[i])*=constant;
        if(vars[i].val == -1) newscores.push(make_pair(act_score[i],i));
    }
    scores = newscores;
}
vector<int> firstUIP(int clause,int level) // get new clause into database
{
    vector<int> newc;
    map<int,bool> exist;
    vector<int> antec,nowc;
    //cout << "---firstUIP---" << endl;
    int p = 0, num =0, maxord =0, prep=0;
    for(int i=0;i<clauses[clause].size();i++) // count the number
    {
        int idx = abs(clauses[clause][i]);
        //cout << idx << ' ' << vars[idx].level << ' ' << vars[idx].order << endl;
        if(vars[idx].level !=0) nowc.push_back(clauses[clause][i]);
        if(vars[idx].level == level) // && vars[idx].order!=1
        {
            num+=1;
            if(vars[idx].order > maxord)
            {
                maxord = vars[idx].order;
                p = idx;
            }
        }
    }
    if(num <= 1) return nowc;
    antec = clauses[vars[p].implyc];
    
    do // clause has more than one literal assigned at current decision level
    {
        newc = vector<int>();
        exist = map<int,bool>();
        antec = clauses[vars[p].implyc];
        prep=0, num=0, maxord=0;
        
        // RESOLVE (C, antec(p), p)
        for(int i=0;i<nowc.size();i++)
        {
            if(abs(nowc[i])!= p && exist[nowc[i]] == false && vars[abs(nowc[i])].level !=0)
            { 
                newc.push_back(nowc[i]);
                exist[nowc[i]] = true;
                if(vars[abs(nowc[i])].level == level) // && vars[abs(newc[i])].order !=1
                {
                    //cout << 'd' << newc.size() << endl;
                    num +=1;
                    if(vars[abs(nowc[i])].order > maxord)
                    {
                        maxord = vars[abs(nowc[i])].order;
                        prep = abs(nowc[i]);
                    }
                }
            }       
        }
        for(int i=0;i<antec.size();i++)
        {
            if(abs(antec[i])!= p && exist[antec[i]] == false && vars[abs(antec[i])].level !=0) 
            {
                newc.push_back(antec[i]);
                exist[antec[i]] = true;
                if(vars[abs(antec[i])].level == level) // && vars[abs(newc[i])].order !=1
                {
                    num +=1;
                    if(vars[abs(antec[i])].order > maxord)
                    {
                        maxord = vars[abs(antec[i])].order;
                        prep = abs(antec[i]);
                    }
                }
            }
        }
        nowc = newc;
        p = prep;
    }while(num > 1);
    return newc;
}
int backlevel(vector<int> clause,int level)
{
    int maxlev = 0;
    checkbigger = false;
    if(clause.size() == 1) // WHEN CLAUSE'S SIZE IF BIGGER THAN 50: DISCARD
    {
        return 0;
    }
    if(clause.size()>50)
    {
        checkbigger = true;
        return 0;
    }
    for(int i=0;i<clause.size();i++)
    {
       // cout << clause[i] << ' ' << vars[abs(clause[i])].level << ' ' << vars[abs(clause[i])].order << endl;
        if(vars[abs(clause[i])].level != level) // || (vars[abs(clause[i])].level == level && vars[abs(clause[i])].order == 1)
        {
            maxlev = max(maxlev,vars[abs(clause[i])].level);
        }
    }
    if(maxlev == 0 && clause.size()!=1) return level;
    return maxlev;
}
bool DPLL() //ITERATIVE DPLL
{
    // ---DECLARE---
    int level = 0, back_level = 0, conflict_clause = 0; //begin assign from level one
    deque<int> tmpassign; // record assignment in this level
    priority_queue<pair<double,int> > decision; // store the scores of variables
    map<int,set<int> > save; // record all assignv in each level
    map<int,vector<variable> > levelvars;
    vector<int> decide;
    bool conflict = false;
    int varidx = 0;
    bool check = false;
    
    // ---FIRST LEVEL ASSIGN (FROM PROBLEM GIVEN)---
    set_UNIT(tmpassign);
    if(BCPLiteralWatching(level,tmpassign)!=-1)
    {
        // if conflict with assignments at level one --> UNSAT
        return false;
    }
    save[level]=assignv; // save assign variable in level 0
    levelvars[level]=vars;
    // ---INITIAL Heuristic SCORES---
    act_score.push_back(0.0);
    for(int i=1;i<=maxVarIndex;i++)
    {
        act_score.push_back(0.0);
        if(vars[i].val == -1) decision.push(make_pair(0.0,i));
    }
    // ---BEGIN SOLVING---
    while(!decision.empty())
    {
        if(assignv.size() == maxVarIndex)
        {
            for(int i=0;i<clauses.size();i++)
                for(int j=0;j<clauses[i].size();j++)
                {
                    if((clauses[i][j]<0 && vars[abs(clauses[i][j])].val == 0) || (clauses[i][j]>0 && vars[abs(clauses[i][j])].val == 1))
                    {
                        satv.insert(i);
                    }
                }
        }
        if(satv.size() == clauses.size()) return true; //every var have been assign and all clauses became SAT
        
        // --- BEGIN ---
        if(!check)
        {
            tmpassign = deque<int>();
            satv = set<int>();
            
            if(!conflict)
            {
                varidx = decision.top().second;
                decision.pop();
                if(vars[varidx].val != -1)
                {
                    assignv.insert(varidx);
                    continue;
                }
                decide.push_back(varidx);
                level +=1;
            }
            else
            {
                varidx = decide.back();
            }
            //cout << "no continue" << endl;
            if(vars[varidx].val != -1) continue;
            if(!conflict) vars[varidx].val =0;
            else vars[varidx].val = 1;
            vars[varidx].level = level;
            vars[varidx].order = 1;
            tmpassign.push_front(varidx);
            assignv.insert(varidx);
            
        }
        // BCP
        conflict_clause = BCPLiteralWatching(level,tmpassign);
        if(conflict_clause == -1) // No conflict
        {
            // cout << "No conflict!" << endl;
            save[level]=assignv;
            levelvars[level]=vars;
            conflict = false;
            check = false;
            continue;
        }
        else // CONFLICT
        {
            // cout << "Conflict1" << endl;
            vector<int> newclause = firstUIP(conflict_clause,level);
            if(newclause.size()==0) return false;
            //cout << "newclause.size: " << newclause.size() << endl;
            back_level = backlevel(newclause,level); // get back level
            level = back_level;

            if(back_level == 0) // EVERYTHING START FORM BEGINNING
            {

                conflict = false; 
                vars = levelvars[0];
                if(!checkbigger)
                {
                    if(newclause[0]>0) vars[newclause[0]].val =1;
                    else vars[abs(newclause[0])].val =0;
                    vars[abs(newclause[0])].level =0;
                    new_watch(newclause);
                }
                decide = vector<int>(); // clear decide
                heuristic(decision,newclause);
                assignv = save[0];
                assignv.insert(abs(newclause[0]));
                save[0]=assignv;
                levelvars[0]=vars;
                tmpassign.push_front(abs(newclause[0]));
                //assignv.insert(abs(newclause[0]));
                check = true;
            } 
            else // BACK TO THE LEVEL
            {
                conflict =true; // guess 1 next time
                vars = levelvars[back_level-1];
                new_watch(newclause);
                decide.resize(back_level);
                heuristic(decision,newclause); // Get Heuristic Scores
                assignv = save[back_level];
                check = false;
            }
        }
    }

    //check last time
    if(assignv.size() == maxVarIndex)
        {
            for(int i=0;i<clauses.size();i++)
                for(int j=0;j<clauses[i].size();j++)
                {
                    if((clauses[i][j]<0 && vars[abs(clauses[i][j])].val == 0) || (clauses[i][j]>0 && vars[abs(clauses[i][j])].val == 1))
                    {
                        satv.insert(i);
                    }
                }
        }
    if(satv.size() == clauses.size()) return true; //every var have been assign and all clauses became SAT
    else return false;
    
}
int main(int argc, const char * argv[]) {
    
    ///---argv
    string input = argv[1];
    ///!!!!!!!!!!!!!!!!!!!!!!THIS MUST CHANGE
    string filename = input.substr(0,input.length()-4) + ".sat";
    fstream outfile;
    int start_time=clock();
    outfile.open(filename.c_str(),ios::out);
    ///---declare variables
    priority_queue<pair<double,int> > decision;
    
    ///---read input files(.cnf)
    parse_DIMACS_CNF(clauses, maxVarIndex, input.c_str());
    
    //heuristic
    initial_watch();
    initial_var();
    // //set_UNIT();
    if(!DPLL())
    {
        cout << "s UNSATISFIABLE" << endl;
        outfile << "s UNSATISFIABLE" << endl;
    }
    else
    {
        cout << "s SATISFIABLE" << endl;
        outfile << "s SATISFIABLE" << endl;
        outfile << "v ";
        for(int i=1;i<=maxVarIndex;i++)
        {
            if(vars[i].val == -1) vars[i].val=0;
            if(vars[i].val == 1) outfile << i << ' ';
            else outfile << -i << ' ';
        }
        outfile << '0' << endl;
    }
    int end_time = clock();
    //cout << end_time << endl;
    printf("Total run time = %f seconds\n",(end_time-start_time)/(double)CLOCKS_PER_SEC);
    return 0;
}
