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
};
vector<vector<int> > pw,nw;
vector<pair<int,int> > watch; // watching literal in clauses
vector<variable> vars,assign; // var status ( for 2 literal watching )
vector<int> unit; //unit clauses
//deque<variable> tmpassign;
deque<int> tmpassign;

set<int> satv,assignv;



void initial_watch()
{
    for(int i=0;i<clauses.size();i++) // watch
    {
        //sat[i] = false; // inital clauses to unsatified
        if(clauses[i].size()>=2) watch.push_back(make_pair(clauses[i][0],clauses[i][1]));
        else if(clauses[i].size()==1){  // clause only have one literal
            watch.push_back(make_pair(clauses[i][0],0));
            unit.push_back(clauses[i][0]); //unit clauses
        }
    }
}
void initial_var()
{
    // initial var & watch
    variable zero;
    vars.push_back(zero);
    vector<int> zeropw,zeronw;
    pw.push_back(zeropw),nw.push_back(zeronw);

    for(int i=1;i<=maxVarIndex;i++) // vars
    {
        variable tmpv;
        vector<int> tmppw,tmpnw;
        
        tmpv.idx = i;
        tmpv.val = -1; //unassign
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
void set_UNIT()
{
    for(int i=0;i<unit.size();i++)
    {
        int v = unit[i];
        if(v>0) vars[v].val = 1;
        else if(v<0) vars[-v].val = 0;
        assign.push_back(vars[abs(v)]); //global assigned variables
        //tmpassign.push_front(vars[abs(v)]); //assigned variables
        tmpassign.push_front(abs(v));
    }
}

bool BCPLiteralWatching()
{
    while(!tmpassign.empty()) // check whether new imply varibles can imply new variables
    {
        //variable tmpv = tmpassign.front();
        //tmpassign.pop_front();
        int tmpi = tmpassign.front();
        tmpassign.pop_front();

        if(vars[tmpi].val == -1 && vars[tmpi].preval != -1)
        {
            vars[tmpi].val = vars[tmpi].preval;
            vars[tmpi].preval = -1;
        }

        // if(tmpv.preval != -1 && tmpv.val == -1) 
        // {
        //     tmpv.val = tmpv.preval;
        //     vars[tmpv.idx].val = tmpv.preval;
        //     vars[tmpv.idx].preval = -1; // recover
        // }
        deque<int>::iterator posf = find(tmpassign.begin(), tmpassign.end(), tmpi);
        //deque<variable>::iterator negf = find(tmpassign.begin(), tmpassign.end(), -tmpv.idx);
        if( posf!=tmpassign.end() && ((vars[tmpi].val == 0 && vars[tmpi].preval == 1) || (vars[tmpi].val == 1 && vars[tmpi].preval == 0))) 
            return false;

        //assign.push_back(tmpv); // assigned variable (global)
        if(vars[tmpi].val == 1) // if val == 1 : check nw clauses
        {
            vector<int> deletions;
            for(int i=0;i<pw[tmpi].size();i++) satv.insert(pw[tmpi][i]);
            for(int i=0;i<nw[tmpi].size();i++) // check every clauses stored in nw
            {
                vector<int> c = clauses[nw[tmpi][i]];
                bool next = false, issat = false, first = false;
                if(tmpi == abs(watch[nw[tmpi][i]].first)) first = true; // var appear at first watch literal
                for(int j=0;j<c.size();j++)
                {
                    //check if not-assigned, not-watched
                    int tmpidx = c[j];

                    if((tmpidx > 0 && vars[tmpidx].val == 1) || (tmpidx < 0 && vars[abs(tmpidx)].val == 0)) issat = true;
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
                    //sat[tmpv.nw[i]] = true; // become sat
                    satv.insert(nw[tmpi][i]);
                }
                else if(vars[abs(vind)].val == -1)
                {
                    if(vind >0) vars[abs(vind)].preval = 1;
                    else vars[abs(vind)].preval = 0;

                    assignv.insert(abs(vind));
                    //tmpassign.push_front(vars[abs(vind)]);
                    tmpassign.push_front(abs(vind));
                }
                else if( ((vind > 0 && vars[abs(vind)].val == 0) || (vind < 0 && vars[abs(vind)].val == 1)) && !issat) // conflict
                {
                    //cout << "false" << endl;
                    for(int j=0;j<deletions.size();j++) 
                    {
                        nw[tmpi].erase(remove(nw[tmpi].begin(),nw[tmpi].end(),deletions[j]),nw[tmpi].end());
                    }
                    return false;
                }
            }
            //erase by value
            for(int j=0;j<deletions.size();j++) 
            {
                nw[tmpi].erase(remove(nw[tmpi].begin(),nw[tmpi].end(),deletions[j]),nw[tmpi].end());
            }
        }
        else if(vars[tmpi].val == 0)
        {
            vector<int> deletions;
            for(int i=0;i<nw[tmpi].size();i++) satv.insert(nw[tmpi][i]);
            for(int i=0;i<pw[tmpi].size();i++) // check every clauses stored in pw
            {
                vector<int> c = clauses[pw[tmpi][i]];
                bool next = false, issat = false, first = false;
                if(tmpi == abs(watch[pw[tmpi][i]].first)) first = true; // var appear at first watch literal
                
                for(int j=0;j<c.size();j++)
                {
                    int tmpidx = c[j];
                    if((c[j] > 0 && vars[tmpidx].val == 1) || (c[j] < 0 && vars[abs(tmpidx)].val == 0)) issat = true;
                    if(vars[abs(tmpidx)].val == -1 && tmpidx!=watch[pw[tmpi][i]].first && tmpidx!=watch[pw[tmpi][i]].second)
                    {
                        if(first) watch[pw[tmpi][i]].first = tmpidx;
                        else watch[pw[tmpi][i]].second = tmpidx;

                        //reset pw & nw
                        
                        if(tmpidx >0) pw[tmpidx].push_back(pw[tmpi][i]); //reset pw
                        else nw[-tmpidx].push_back(pw[tmpi][i]); // reset nw
                        
                        //record deletions' index
                        deletions.push_back(pw[tmpi][i]);
                        next = true;
                        break;
                    }
                    
                }
                if(next) continue;//next watching literal is setted
                
                int vind =0; //another watch literal
                if(first) vind = watch[pw[tmpi][i]].second;
                else vind = watch[pw[tmpi][i]].first;
                if((vind > 0 && vars[abs(vind)].val == 1) || ((vind < 0 && vars[abs(vind)].val == 0)) || issat)
                {
                    satv.insert(pw[tmpi][i]);
                }
                else if(vars[abs(vind)].val == -1)
                {
                    if(vind >0) vars[abs(vind)].preval = 1;
                    else vars[abs(vind)].preval = 0;
                    assignv.insert(abs(vind));
                    //tmpassign.push_front(vars[abs(vind)]);
                    tmpassign.push_front(abs(vind));
                }
                else if( ((vind > 0 && vars[abs(vind)].val == 0) || (vind < 0 && vars[abs(vind)].val == 1)) && !issat) // conflict
                {
                    for(int j=0;j<deletions.size();j++) 
                    {
                        pw[tmpi].erase(remove(pw[tmpi].begin(),pw[tmpi].end(),deletions[j]),pw[tmpi].end());
                    }
                    return false;
                }
            }
            //erase by value
            for(int j=0;j<deletions.size();j++) 
            {
                pw[tmpi].erase(remove(pw[tmpi].begin(),pw[tmpi].end(),deletions[j]),pw[tmpi].end());
            }
        }

    }
    return true;
}

bool dpllSimple(priority_queue<pair<double,int> > &decision)
{
    if(!BCPLiteralWatching())
    {
        return false;
    }
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
    if(satv.size() == clauses.size()) return true; //every var have been assign

    vector<variable> oldvars;
    set<int> oldset = satv, oldassign=assignv;;
    //tmpassign = deque<variable>();
    tmpassign = deque<int>();
    satv = set<int>();
    oldvars = vars; // save old pattern

    while(!decision.empty())
    {
        //making decision
        int varidx = decision.top().second;
        decision.pop();
        priority_queue<pair<double,int> > tmpdecision = decision;
        
        if(vars[varidx].val != -1) continue;
        
        vars[varidx].val = 0; // decide 0
        assignv.insert(varidx);
        //tmpassign.push_front(vars[varidx]);
        tmpassign.push_front(varidx);

        if(dpllSimple(tmpdecision))
        {
            if(satv.size() == clauses.size()) return true; //SAT
            continue;
        }
        vars = oldvars; // back to old pattern
        satv = oldset;
        assignv = oldassign;
        tmpdecision = decision;
        //tmpassign = deque<variable>();
        tmpassign = deque<int>();
        satv = set<int>();

        vars[varidx].val = 1; // decide 1
        assignv.insert(varidx);
        //tmpassign.push_front(vars[varidx]);
        tmpassign.push_front(varidx);
        if(dpllSimple(tmpdecision))
        {
            if(satv.size() == clauses.size()) return true; //SAT
            continue;
        }
        else
        {
            vars = oldvars; // back to old pattern
            satv = oldset;
            assignv = oldassign;
            //tmpassign = deque<variable>();
            tmpassign = deque<int>();
            satv = set<int>();
            return false;
        }
    }
    if(satv.size() == clauses.size()) return true;
    else return false;
}


void heuristic(priority_queue<pair<double,int> > &scores)
{
    for(int i=1;i<=maxVarIndex;i++)
    {
        double score=0.0;
        for(int j=0;j<clauses.size();j++)
        {
            vector<int>::iterator posit,negit;
            posit = find(clauses[j].begin(),clauses[j].end(),i);
            negit = find(clauses[j].begin(),clauses[j].end(),-i);
            
            if(posit != clauses[j].end() || negit != clauses[j].end())
            {
                double s = clauses[j].size();
                score += pow(2,-s);
            }
        }
        scores.push(make_pair(score,i));
    }
}

int main(int argc, const char * argv[]) {
    
    ///---argv
    string input = argv[1];
    string filename = input.substr(0,input.length()-4) + "_out" + ".txt";
    fstream outfile;
    int start_time=clock();
    outfile.open(filename.c_str(),ios::out);
    ///---declare variables
    priority_queue<pair<double,int> > decision;

    ///---read input files(.cnf)
    parse_DIMACS_CNF(clauses, maxVarIndex, input.c_str());


    //heuristic
    heuristic(decision);
    initial_watch();
    initial_var();
    set_UNIT();
    
    if(!dpllSimple(decision)) 
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
