\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{inprogress}[2024/01/10 Jaume's minimal WIP template on top of article]

\LoadClass{article}

\DeclareOption{noproofs}{
    \RequirePackage{environ}
    \NewEnviron{killcontents}{}
    \let\proof\killcontents
    \let\endproof\endkillcontents
}
\DeclareOption{showlabels}{
    \RequirePackage{showlabels}
}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  Packages
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Meta
\RequirePackage{xkeyval}

%Encoding
\RequirePackage[normalem]{ulem}
\RequirePackage[english]{babel}
\RequirePackage[utf8]{inputenc}

%URL & Code
\RequirePackage{url}
\RequirePackage{verbatim}

% Math
\RequirePackage{amsthm,amssymb,amsmath}
\RequirePackage{esint}
\RequirePackage{bbm}

% Color & Prettyness
\RequirePackage{graphicx}
\RequirePackage[dvipsnames]{xcolor}
\RequirePackage{scalerel}

% Page & Organization
\RequirePackage{fullpage}
\RequirePackage{enumitem}
\RequirePackage{hyperref}
\RequirePackage{cleveref}

% Work in progress 
% Todo: Add lineno as option, and noproofs.
\RequirePackage{lineno}
\linenumbers
\RequirePackage{todonotes}
%\usepackage{showlabels}
%\usepackage{environ}
%NewEnviron{killcontents}{}
%\let\proof\killcontents
%\let\endproof\endkillcontents


% Usual types of theorems

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{goal}[theorem]{Goal}

\theoremstyle{definition}
\newtheorem{remark}[theorem]{Remark}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{conjecture}[theorem]{Conjecture}

%Usual commands


\DeclareMathOperator*{\argmax}{arg\,max}
\DeclareMathOperator*{\argmin}{arg\,min}
\newcommand{\osc}[1][{}]{\operatorname{Osc}_{{#1}}}

\newcommand{\dd}{\mathop{}\!\mathrm{d}}
\newcommand{\1}{\mathbbm{1}}

\newcommand{\RR}{{\mathbb{R}}}
\newcommand{\CC}{{\mathbb{C}}}
\newcommand{\ZZ}{{\mathbb{Z}}}
\newcommand{\NN}{{\mathbb{N}}}
\renewcommand{\SS}{{\mathbb{S}}}

\newcommand{\warning}[1]{\textbf{\color{red}{#1}}}


% Begin custom author code
\makeatletter

\definecolor{personcolor}{rgb}{1, 0, 0}

% Initialize \@author to be empty
\def \newauthor@fullname{}
\def\@author{\newauthor@fullname} 


% Define keys for author information
\define@key{newauthor}{fullname}{
    \ifx\newauthor@fullname\@empty
        \def\newauthor@fullname{#1}
    \else
    \g@addto@macro\newauthor@fullname{\and #1}
    \fi
}
\define@key{newauthor}{institution}{\def\newauthor@institution{#1}}
\define@key{newauthor}{email}{\def\newauthor@email{#1}}

% Redefine the \author command with key-value options
\newcommand{\newauthor}[2][]{%
  % Process the key-value options
  \setkeys{newauthor}{#1}%

  % Create a personalized command \shortname{...}
  \expandafter\newcommand\csname #2\endcsname[1]{%
    {\color{personcolor}{\textbf{#2}:} ##1}%
  }
}

\makeatother