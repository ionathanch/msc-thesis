%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ubcdiss.cls: A LaTeX document class for the revised UBC Thesis Guidelines
%% Originally created by Brian de Alwis.  I developed this separately from
%% Michael McNeil Forbes's ubcthesis.cls/genthesis.class: unlike Forbes' class,
%% this class builds on top of the standard LaTeX book class and should have
%% better compatibility with standard LaTeX packages.
%%
%% GPS Thesis Specifications and Formatting Requirements
%% <https://www.grad.ubc.ca/current-students/dissertation-thesis-preparation/structure-theses-dissertations>
%% <https://www.grad.ubc.ca/current-students/dissertation-thesis-preparation/formatting-requirements>
%% 
%% Useful documents:
%%  * LaTeX2e for class and package writers
%%    <http://www.latex-project.org/guides/clsguide.pdf>
%%
%% This package, and all its contents, are placed in the public domain.
%% 

%% Options that can be specified with the documentclass:
%%   singlespacing     typeset text single spaced
%%   onehalfspacing    typeset text line-and-a-half spacing
%%   doublespacing     typeset text double spaced
%%   10pt              use a 10pt font
%%   11pt              use a 11pt font (default)
%%   12pt              use a 12pt font
%%   oneside           arrange pages for single-sided printing (default)
%%   twoside           insert blank pages as required for double-sided printing

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{ubcdiss}[2022/02/22]

% default line spacing in \textspacing
\newcommand{\textspacing}{\singlespacing}
\DeclareOption{singlespacing}{\renewcommand{\textspacing}{\singlespacing}}
\DeclareOption{onehalfspacing}{\renewcommand{\textspacing}{\onehalfspacing}}
\DeclareOption{doublespacing}{\renewcommand{\textspacing}{\doublespacing}}

\DeclareOption{10pt}{\PassOptionsToClass{10pt}{book}}
\DeclareOption{11pt}{\PassOptionsToClass{11pt}{book}}
\DeclareOption{12pt}{\PassOptionsToClass{12pt}{book}}
\DeclareOption{oneside}{\PassOptionsToClass{oneside}{book}}
\DeclareOption{twoside}{\PassOptionsToClass{twoside,openright}{book}}

\ExecuteOptions{11pt,oneside}
\ProcessOptions\relax
\LoadClass[letterpaper]{book}

\RequirePackage{calc}
\RequirePackage{textcase} % upper-/lower-casing
\RequirePackage{setspace} % line spacing
\RequirePackage{tocbibind} % ToC with LoT, LoF, biblio, index
\RequirePackage[titles]{tocloft} % ToC, LoT, LoF typesetting
\RequirePackage{fancyhdr} % custom headers and footers

% ToC full name
\renewcommand{\contentsname}{Table of Contents}

% ToC leader dots
\renewcommand{\cftpartdotsep}{\cftdotsep}
\renewcommand{\cftchapdotsep}{\cftdotsep}

% prefix entries in LoT and LoF with Table/Figure
\setlength{\cfttabindent}{0em}
\setlength{\cftfigindent}{0em}
\renewcommand{\cfttabpresnum}{Table }
\renewcommand{\cftfigpresnum}{Figure }
\addtolength{\cfttabnumwidth}{\widthof{\cfttabfont\cfttabpresnum~}}
\addtolength{\cftfignumwidth}{\widthof{\cfttabfont\cfttabpresnum~}}

% From <http://dcwww.camd.dtu.dk/~schiotz/comp/LatexTips/LatexTips.html#figplacement>
% LaTeX per default only allows a part of the top of a text-page
% (70%) to contain figures, and requires at least 20% of a page to
% be text when text and figures share a page. These parameters should
% be set to more reasonable values, for example 85% and 10%.  Be careful
% not to make \floatpagefraction larger than \topfraction, then you
% risk to produce a figure that can neither go on the top of a text
% page, nor on a page by itself.
\renewcommand{\topfraction}{0.85}
\renewcommand{\textfraction}{0.1}
\renewcommand{\floatpagefraction}{0.75}

% no headers, centre bottom page number
\pagestyle{plain}

% Useful command stolen from Forbes' genthesis.cls
\newcommand{\@addto}[2]{
  \expandafter\let\expandafter\old\csname#1\endcsname
  \toks1=\expandafter{\old}
  \toks2=\expandafter{#2}
  \expandafter\xdef\csname#1\endcsname{\the\toks1 \the\toks2 }
}

% defaults
\newcommand*{\@subtitle}{}
\newcommand*{\@previousdegrees}{}
\newcommand{\@degreetitle}{%
    \ClassError{ubcdiss}{Missing degree title}{%
	Specify \protect\degreetitle\space in your dissertation
	metadata section.}
    \emph{missing degree title}}
\newcommand{\@institution}{The University of British Columbia}
\newcommand{\f@culty}{Graduate and Postdoctoral Studies}
\newcommand*{\dep@rtment}{}
\newcommand{\c@mpus}{%
    \ClassError{ubcdiss}{Missing campus name}{%
	Specify \protect\campus\{\}\space in your dissertation
	metadata section.}%
    \emph{missing campus}}
\newcommand{\@subye@r}{
    \ClassError{ubcdiss}{Missing submission year}{%
	Specify \protect\submissionyear\space in your dissertation
	metadata section.}
    \emph{missing submission year}}
\newcommand{\@submonth}{
    \ClassError{ubcdiss}{Missing submission month}{%
	Specify \protect\submissionmonth\space in your dissertation
	metadata section.}
    \emph{missing submission month}}

\newcommand{\subtitle}[1]{\renewcommand{\@subtitle}{#1}}
\newcommand{\previousdegree}[1]{\@addto{@previousdegrees}{#1\par}}
\newcommand{\degreetitle}[1]{\renewcommand{\@degreetitle}{#1}}
\newcommand{\institution}[1]{\renewcommand{\@institution}{#1}}
\newcommand{\faculty}[1]{\renewcommand{\f@culty}{#1}}
\newcommand{\department}[1]{\renewcommand{\dep@rtment}{#1}}
\newcommand{\program}[1]{\department{#1}}
\newcommand{\campus}[1]{\renewcommand{\c@mpus}{#1}}
\newcommand{\submissionyear}[1]{\renewcommand{\@subye@r}{#1}}
\newcommand{\submissionmonth}[1]{\renewcommand{\@submonth}{#1}}

\renewcommand{\date}[1]{%
    \ClassWarning{ubcdiss}{Ignoring \protect\date:
	use \protect\submissionyear and \protect\submissionmonth instead}}

\renewcommand{\maketitle}{%
    \frontmatter
    \thispagestyle{empty}
    \begin{titlepage}
    \begin{center}
    \begin{doublespace}
    {\Large \textbf{\@title}}\\\medskip
	\ifx\@subtitle\empty\relax\else{\large\textbf{\@subtitle}}\\\medskip\fi

	{\large by}\\\medskip
	{\large \@author}\\\medskip
	\ifx\@previousdegrees\empty\vspace{0.5\baselineskip}\else\@previousdegrees\\\bigskip\fi

	{\Large \textsc{a thesis submitted in partial fulfillment}}\\
	{\Large \textsc{of the requirements for the degree of}}\\\medskip
	{\large \textbf{\@degreetitle}}\\\medskip

	{\large in}\\\medskip
	{\Large \textsc{\MakeTextLowercase{\f@culty}}}\\
	\ifx\dep@rtment\empty\vspace{\baselineskip}\else{\large (\dep@rtment)}\\\bigskip\fi

	{\Large \textsc{\MakeTextLowercase{\@institution}}}\\
	{\large (\c@mpus)}\\\bigskip
	{\large \@submonth\ \@subye@r}

    \vfill
	{\large \textcopyright\ \@author, \@subye@r}
    \end{doublespace}
    \end{center}
    \end{titlepage}
    \setcounter{page}{2}
    \renewcommand{\frontmatter}{\ClassError{ubcdiss}{frontmatter should not be used}}
}

\newcommand*{\ex@miners}{}
\newcommand*{\@supervisory}{}
\newcommand{\examiningcommittee}[2]{\@addto{ex@miners}{
    \par\medskip\noindent#1\\\emph{#2}}}
\newcommand{\supervisorycommittee}[2]{\@addto{@supervisory}{
    \par\medskip\noindent#1\\\emph{#2}}}
\newcommand{\makecommitteepage}{
    \begin{singlespace}
    \noindent The following individuals certify that they have read,
    and recommend to the Faculty of Graduate and Postdoctoral Studies
    for acceptance, the thesis entitled:
    \par\bigskip
    {\large \textbf{\@title\ifx\@subtitle\empty\relax\else: \@subtitle\fi}}
    \par\bigskip\noindent
    submitted by
	\textbf{\@author}
    in partial fulfillment of the requirements for the degree of
	\textbf{\@degreetitle}
    in
	\textbf{\ifx\dep@rtment\empty\f@culty\else\dep@rtment\fi}.
    \par\bigskip\noindent
    \textbf{Examining Committee:}
    \ex@miners
    \ifx\@supervisory\empty\relax\else
        \par\bigskip\noindent
        \textbf{Additional Supervisory Committee Members:}
        \@supervisory
    \fi
    \end{singlespace}
    \cleardoublepage
}