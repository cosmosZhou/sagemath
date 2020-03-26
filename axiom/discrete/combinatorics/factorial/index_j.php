<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left\\{*x\\right\\}  = \\left[0; n\\right)\\tag*{Eq[0]}\\)\\({x}_{[k:n]\\delta_{j {x}_{k}} \\times [k:n]k} = j\\tag*{Eq[0]=>Eq[1]}\\)";
$txt[$i++] = "\\([k:n]\\delta_{j {x}_{k}} \\times [k:n]k = \\sum\\limits_{k=1}^{n - 1} k \\delta_{j {x}_{k}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\delta_{j {x}_{k}} = \\begin{cases} 1 & \\text{if}\\: j = {x}_{k} \\\\0 & \\text{else} \\end{cases}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\([k:n]\\delta_{j {x}_{k}} \\times [k:n]k = \\sum\\limits_{\\substack{k \\in \\left\\{k \\in \\left[1; n\\right) \\mid j = {x}_{k} \\right\\}}} k\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{k \\in \\left\\{k \\in \\left[0; n\\right) \\mid j = {x}_{k} \\right\\}}} k = \\sum\\limits_{\\substack{k \\in \\left\\{k \\in \\left[1; n\\right) \\mid j = {x}_{k} \\right\\}}} k\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\([k:n]\\delta_{j {x}_{k}} \\times [k:n]k = \\sum\\limits_{\\substack{k \\in \\left\\{k \\in \\left[0; n\\right) \\mid j = {x}_{k} \\right\\}}} k\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(s_{j} = \\left\\{k \\in \\left[0; n\\right) \\mid j = {x}_{k} \\right\\}\\tag*{Eq.sj_definition}\\)";
$txt[$i++] = "\\([k:n]\\delta_{j {x}_{k}} \\times [k:n]k = \\sum\\limits_{\\substack{k \\in s_{j}}} k\\tag*{Eq.sigmar}\\)";
$txt[$i++] = "\\(s_{j} = \\left\\{k \\in \\left[0; n\\right) \\mid {x}_{k} = j \\right\\}\\tag*{Eq.sj_definition_reversed}\\)";
$txt[$i++] = "\\(\\left\\{k \\in \\left[0; n\\right) \\mid {x}_{k} = j \\right\\} = s_{j}\\tag*{Eq.sj_definition_reversed}\\)";
$txt[$i++] = "\\(\\left\\{j\\right\\} \\cap \\left\\{*x\\right\\}  = \\left\\{j\\right\\}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left\\{\\left. {x}_{k} \\right| k \\in \\left\\{k \\in \\left[0; n\\right) \\mid {x}_{k} = j \\right\\} \\right\\} = \\left\\{j\\right\\}\\tag*{Eq.distribute}\\)";
$txt[$i++] = "\\(\\left\\{k \\in \\left[0; n\\right) \\mid {x}_{k} = j \\right\\} \\neq \\emptyset\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(s_{j} \\neq \\emptyset\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\left|{s_{j}}\\right| \\geq 1\\tag*{Eq.sj_greater_than_1}\\)";
$txt[$i++] = "\\(\\left\\{\\left. {x}_{k} \\right| k \\in s_{j} \\right\\} = \\left\\{j\\right\\}\\tag*{Eq.distribute}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\in s_{j}\\\\b \\in s_{j}}}{a \\neq b} \\vee \\left|{s_{j}}\\right| \\leq 1\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\in s_{j}\\\\b \\in s_{j}}}{a \\neq b}\\tag*{~Eq.inequality_ab}\\)";
$txt[$i++] = "\\(\\left|{s_{j}}\\right| \\leq 1\\tag*{Eq.sj_less_than_1}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{l \\in \\left[0; n\\right) \\setminus \\left\\{k\\right\\}}}{{x}_{k} \\neq {x}_{l}}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{l \\in \\left[0; n\\right) \\setminus \\left\\{a\\right\\}}}{{x}_{a} \\neq {x}_{l}}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\(b \\not\\in \\left[0; n\\right) \\setminus \\left\\{a\\right\\} \\vee {x}_{a} \\neq {x}_{b}\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\in s_{j}\\\\b \\in s_{j}}}{a \\neq b\\wedge \\left(b \\not\\in \\left[0; n\\right) \\setminus \\left\\{a\\right\\} \\vee {x}_{a} \\neq {x}_{b}\\right)}\\tag*{~Eq[14]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\in s_{j}\\\\b \\in s_{j}}}{a \\neq b\\wedge {x}_{a} \\neq {x}_{b} \\vee b \\not\\in \\left[0; n\\right) \\cup \\left\\{a\\right\\}}\\tag*{~Eq.distribute_ab}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{k \\in s_{j}}}{j = {x}_{k}}\\tag*{Eq.j_equality}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{k \\in s_{j}}}{k \\in \\left[0; n\\right)}\\tag*{Eq.k_domain}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{a \\in s_{j}}}{\\left[0; n\\right) \\cup \\left\\{a\\right\\} = \\left[0; n\\right)}\\tag*{Eq[15]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{b \\in s_{j}}}{\\exists_{\\substack{a \\in s_{j}}}{a \\neq b\\wedge {x}_{a} \\neq {x}_{b}} \\vee b \\not\\in \\left[0; n\\right)}\\tag*{~Eq[16]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{b \\in s_{j}}}{\\exists_{\\substack{a \\in s_{j}}}{a \\neq b\\wedge {x}_{a} \\neq {x}_{b}}\\wedge b \\in \\left[0; n\\right)}\\tag*{~Eq[17]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
$txt[$i++] = "\\(\\left|{s_{j}}\\right| = 1\\tag*{Eq[18]}\\)";
$txt[$i++] = "\\(\\exists_{a}{s_{j} = \\left\\{a\\right\\}}\\tag*{Eq[19]}\\)";
$txt[$i++] = "\\(\\exists_{a}{[k:n]\\delta_{j {x}_{k}} \\times [k:n]k = a}\\tag*{Eq[20]}\\)";
render(__FILE__, $txt);
?>        

