%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%% INSTRUCTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%% SUMMARY %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%% Introduction of you article
%%%%%%% Bibliography
%%%%%%% Minted and listings
%%%%%%% Packages
%%%%%%% Environments and labelling

%%%%%%%%%%%%%%%%%%%% TEXT %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%% Introduction of you article

%   You should put all these informations below in this order after the document class and before \begin{document}.

%%%% Title and abstract

%  To insert the article title, use the command \title{...}.
%  If your title is too long, you can provide a shorter version in option such as \title[shorter title]{full title}.

%To put the abstract, you need to write it in an environment \begin{abstract} \end{abstract}.

%%%% Authors

%  Authors are listed with the command "\author[F. Author, S. Author]{%
%   First Author, Second Author
%    }"

%  You need for each author to write their information in this format : "\authorinfo[F. Author]{
%   University, Country}{
%   Email
%    }"

%%%% Metadata

%% Provide the following information for the journal (mandatory for successful compilation):

%\VOLUME{}
%\YEAR{}
%\NUMBER{}
%\firstpage{}
%\DOI{}
%\receiveddate{}
%\finaldate{}
%\accepteddate{}

%  Even if you don't have the information, not writing the fields below can lead to critical errors.

%% Other necessary metadatas not causing crash on compilation if not put into your article :

%msc{}

%\keywords{}

%%%%%%% Bibliography

%%% Declaration

% This class uses the bibLaTeX package, so the package natbib will cause incompatibilities if you used it for your article.
% First, you need to write where is you bibligraphy with the line "\addbibresource{name of your bibliography file}"
%   Eventually, write \printbibliography at the end of your article, before \end{document}


%%% Supported entry types

% This class uses BibTeX and requires standard entry types:
%   book, booklet, conference, inbook, incollection, inproceedings,
%   manual, mastersthesis, misc, phdthesis, proceedings, techreport, unpublished

% See: https://www.bibtex.com/e/entry-types for standard layout for each entry

%%% Unsupported entry types

% For entries non listed below for example "software" or "software-engine", use the type "misc" like this :

%"@misc{"your anchor for the biblography",
%  title        = {"your title"},
%  howpublished = {\url{"the site of your program"}},
%  note         = {"informations about your program"\\
%                  SWHID: \small{\texttt{the swhid}};\\
%  year         = {"the year"},
%  crossref     = {"potentially the anchor of another ref which this ref depends"}
%}"

%%% Compilation

% This class needs BibTeX to compile, so, after writing your code, you must compile with pdfLaTeX, then BibTeX, then pdfLaTeX and pdfLaTeX again.

%%%%%%%Minted and listings

%%%How to activate the right language

% Minted and listings are incompatible, by default the class used listings. If you need the package minted, you must add the option [minted] when you declare the AFM class like this : \documentclass[minted]{AFM}.
%  Else, the article will run on listings. If you are using rocq and/or lean, put the name of your language in the option of the class like minted, separated by a comma.

%%% Characters

%  Usuals unicode and greek characters are recognized in each language. If one of you character isn't supported, you can expand the lists by putting this command before starting your document:

%\lstset{literate+=
%  {the character you want}{{the code associated with}}1
%}

% For example:

%\lstset{literate+=
%  {œ}{{\oe}}1
%}

%%% Bloc and inline

%%  listing
%Block : \begin{lstlisting} \end{lstlisting}
%Inline : \lstinline{}

%%  lean
%Block : \begin{lean} \end{lean}
%Inline : \leaninline{}

%%  rocq
%Block : \begin{rocq} \end{rocq}
%Inline : \rocqinline{}

%%%%%%% Packages

%%%% Packages already used in this class

%  The following packages are preloaded by the class:
% geometry, amsmath, amssymb, amsthm, graphicx, fancyhdr, hyperref, dvipsnames,
% microtype, tikz, verbatim, inputenc, fontenc, InriaSerif, gfsbodoni, csquotes,
% biblatex, minted/listings, color, xcolor, enumitem

% Package fullpage tends to erase the headers and footers so you should not use it.

%%%%%%% Environment and labelling

%% Pre-defined environments

% theorem, conjecture, corollary, definition, example, lemma, problem,
% proof, proposition, remark, notation, examples, remarks

%% Harmonizing environment names
%
%  To standardize labels and numbering, if you use a predefined section with another name, you can use the command \equalenv such as:
%   \equalenv{"name you use for you section"}{"name used by the article class"}
%
% Example:
%   \equalenv{tmz}{theorem}

%% If your environment is not affected in the list

%  In the case you want to use an environment which does not belong to the previous list, add your definition such as :

%\newtheorem{environment label}[environment you depend on to do the section count]{name of your environment}

%  For example, if you want an environment Subsublemma, called by the command \begin{sslmma}) you need to modify the definition so that it reads

%\newtheorem{sslmma}[lemma]{Subsublemma}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%   END   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\NeedsTeXFormat{LaTeX2e}
\def\ClassName@AFM{AFM}
\ProvidesClass{AFM}[2024/04/02 v1]




\LoadClass[letterpaper, 12pt, twoside]{article}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions


\RequirePackage{setspace}
\setstretch{1.25}

%%%%% Option Minted %%%%%

\DeclareOption{minted}{\def\options@minted{true}} % Active une variable si l'option est donnée
\ProcessOptions

%%%%% End Minted %%%%%

%%%%% Option lean %%%%%

\DeclareOption{lean}{\def\options@lean{lstlean.sty}} % Active une variable si l'option est donnée
\ProcessOptions

%%%%% Fin lean %%%%%

%%%%% Option rocq %%%%%

\DeclareOption{rocq}{\def\options@rocq{lstrocq.sty}} % Active une variable si l'option est donnée
\ProcessOptions\relax

%%%%% End rocq %%%%%

\newcommand{\lstlanguagefileslist}{}


%%%Loading Packages
\RequirePackage[
    margin=1.07in,
    top=1in,
    % topmargin=.6in,
    bottom=1.33in,
    headheight=170pt,
    footskip=.5in,
    headsep=.15in
]{geometry}
\RequirePackage{graphicx}
\RequirePackage{ifthen}
\RequirePackage{xurl}
\RequirePackage{tabularx}

%%% Colors
\RequirePackage[dvipsnames]{xcolor}
\definecolor{primaire}{HTML}{f05f28}
\definecolor{secondaire}{HTML}{ab2311}
\definecolor{tertiaire}{HTML}{454545}


%%%%% HEADERS AND FOOTERS %%%
\RequirePackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}    % reset everything

\let\oldheadrule\headrule% Copy \headrule into \oldheadrule
\renewcommand{\headrule}{\color{secondaire}\oldheadrule}% Add colour to \headrule
\renewcommand{\headrulewidth}{.5pt}
%	\ifnum\thepage=\thefirstpage@AFM 0pt 0.5pt%
%	\fi}
\def\footnoterule{\kern-3\p@ \hrule \@width1in \kern2.6\p@}

\fancyhead[COH]{\footnotesize \theshort@title }

\fancyhead[CEH]{\footnotesize \theshort@author }


%%% bottom left
\lfoot{\footnotesize
        %\includegraphics[height=6.5mm,clip=true,trim=150 160 150 150]{AFMfooter}
    }


%%% bottom right
\rfoot{\footnotesize
    \ifnum\thepage=\thefirstpage@AFM
        \relax
    \else
            \thepage
    \fi
    }


\fancypagestyle{first}{
\fancyhf{}    % reset everything

\renewcommand{\headrulewidth}{0pt}
\def\footnoterule{\kern-3\p@ \hrule \@width1in \kern2.6\p@}
}
%%%%% END HEADERS AND FOOTERS %%%%%


%%% hyperref %%%
\RequirePackage[%
colorlinks = true,
citecolor = primaire,
linkcolor = secondaire,
urlcolor = blue]{hyperref}
%%%% end hyperref %%%






\RequirePackage[english]{babel}
\RequirePackage{microtype}
\RequirePackage{tikz}
\RequirePackage{verbatim}

\RequirePackage[utf8]{inputenc}

\RequirePackage{amsmath, amssymb, amsthm}

\RequirePackage[scaled]{beramono}

\RequirePackage[bitstream-charter]{mathdesign}
\RequirePackage[scaled]{berasans}
\renewcommand{\sfdefault}{fvs}  % fvs = Bera Sans
\RequirePackage[T1]{fontenc}



\numberwithin{equation}{section}


%%%%Bibliography management

\RequirePackage[
  backend=bibtex,
  style=alphabetic,
  sorting=nty,
  giveninits=true,
  abbreviate=false,
  natbib=true,
  bibencoding=utf8,
  url=true,
  doi=true,
  maxcitenames=10,
  maxbibnames=100
]{biblatex}

%%%Definition of the electronic identifiers for the articles
\DeclareFieldFormat{eid}{Art. \addnbspace #1}


%%%Definition of the electronic for the quantity of pages for the articles
\DeclareFieldFormat[article]{pagetotal}{\mkpagetotal[pagination]{#1}}
\renewbibmacro*{note+pages}{%
  \printfield{note}%
  \setunit{\bibpagespunct}%
  \printfield{pages}%
  \setunit{\bibpagespunct}%
  \printfield{pagetotal}%
  \newunit}


\RequirePackage{csquotes}

%%% end bibliography management %%%


%%%%%% Code environment management %%%%
\ifdefined\AFM@minted
    \RequirePackage{minted} % Use minted if activated

\else

    \RequirePackage{listings} % Else, use listings


%Debug literate+=
\define@key{lst}{literate+}{%
  \expandafter\def\expandafter\lst@literate\expandafter{%
    \lst@literate#1}%
}


%%% Color code
\usepackage{color}
%%%color of lean
\definecolor{keywordcolor}{rgb}{0.7, 0.1, 0.1}   % red
\definecolor{commentcolor}{rgb}{0.4, 0.4, 0.4}   % grey
\definecolor{symbolcolor}{rgb}{0.0, 0.1, 0.6}    % blue
\definecolor{sortcolor}{rgb}{0.1, 0.5, 0.1}      % green
%%%color of rocq
\definecolor{ltblue}{rgb}{0,0.4,0.4}
\definecolor{dkblue}{rgb}{0,0.1,0.6}
\definecolor{dkgreen}{rgb}{0,0.35,0}
\definecolor{dkviolet}{rgb}{0.3,0,0.5}
\definecolor{dkred}{rgb}{0.5,0,0}

%%% activation of the language rocq and lean put in the option
\def\lstlanguagefiles{\options@lean, \options@rocq}

\ifdefined\options@rocq
\lstset{language=rocq}

\def\rocqinline{\lstinline[language=rocq, basicstyle=\lst@ifdisplaystyle\scriptsize\fi]}

\fi

\ifdefined\options@lean
\lstnewenvironment{lean}{\lstset{language=lean}}{} %%%Attention basicstyle=\ttfamily
\def\leaninline{\lstinline[language=lean, basicstyle=\lst@ifdisplaystyle\scriptsize\fi]}

\fi
%%% end of activation of the language rocq and lean put in the option


\lstset{
    inputencoding=utf8,
    mathescape,
    extendedchars=true,
    mathescape=true,
    literate=%
    {á}{{\'a}}1
    {č}{{\v{c}}}1
    {ď}{{\v{d}}}1
    {é}{\texttt{\'e}}1
    {ě}{{\v{e}}}1
    {í}{{\'i}}1
    {ň}{{\v{n}}}1
    {ó}{{\'o}}1
    {ř}{{\v{r}}}1
    {š}{{\v{s}}}1
    {ť}{{\v{t}}}1
    {ú}{{\'u}}1
    {ů}{{\r{u}}}1
    {ý}{{\'y}}1
    {ž}{{\v{z}}}1
    {Á}{{\'A}}1
    {Č}{{\v{C}}}1
    {Ď}{{\v{D}}}1
    {É}{{\'E}}1
    {Ě}{{\v{E}}}1
    {Í}{{\'I}}1
    {Ň}{{\v{N}}}1
    {Ó}{{\'O}}1
    {Ř}{{\v{R}}}1
    {Š}{{\v{S}}}1
    {Ť}{{\v{T}}}1
    {Ú}{{\'U}}1
    {Ů}{{\r{U}}}1
    {Ý}{{\'Y}}1
    {Ž}{{\v{Z}}}1
    {è}{{\`{e}}}1
    {ê}{{\^{e}}}1
    {ë}{{\¨{e}}}1
    {É}{{\'{E}}}1
    {Ê}{{\^{E}}}1
    {û}{{\^{u}}}1
    {ù}{{\`{u}}}1
    {ú}{{\'{u}}}1
    {â}{{\^{a}}}1
    {à}{{\`{a}}}1
    {á}{{\'{a}}}1
    {ã}{{\~{a}}}1
    {Á}{{\'{A}}}1
    {Â}{{\^{A}}}1
    {Ã}{{\~{A}}}1
    {ç}{{\c{c}}}1
    {Ç}{{\c{C}}}1
    {õ}{{\~{o}}}1
    {ó}{{\'{o}}}1
    {ô}{{\^{o}}}1
    {Õ}{{\~{O}}}1
    {Ó}{{\'{O}}}1
    {Ô}{{\^{O}}}1
    {î}{{\^{i}}}1
    {Î}{{\^{I}}}1
    {í}{{\'{i}}}1
    {=}{$\leftarrow$}{1}
    {==}{$={}$}{1},
    basicstyle=\small,
    stringstyle=\ttfamily,
}

\fi

%%%%%% End of code environment management %%%%






%%%lists
\RequirePackage[inline]{enumitem}
\setlist[enumerate,1]{label=(\arabic*), ref =(\arabic*)}
\setlist[enumerate,2]{label=(\emph{\roman*}), ref =(\emph{\roman*})}
\setlist[enumerate,2]{label=(\emph{\alph*}), ref =(\emph{\alph*})}
\setlist{noitemsep}
%%%%don't forget to document \begin{enumerate*}...\end{enumerate*}
%%%%%%



%%% AUXILIARY MACROS %%%

% Definitions of 'newfield's macros.
\def\newfield@AFM{\@ifnextchar*\newfieldB@AFM\newfieldA@AFM}

% If \newfield@AFM is not followed by a *, then:
% newfield@AFM defines a macro called '\#1' which defines a macro '\the@#1'
\def \newfieldA@AFM #1{%
    \def#1##1{%
        \escapechar`\@ \relax
        \long\@namedef{the\string#1}{##1}
        \escapechar=92
        }
    }

% If \newfield@AFM is followed by a *, then:
% newfield@AFM defines a macro called '\#1', which has one or two arguments.
% The first argument is optional and defines a macro called '\theshort@#1';
% the second argument is mandatory and defines a macro called '\the@#1'.
\def\newfieldB@AFM*#1{%
    \def#1{\@ifnextchar[{\@nameuse{\string#1@B}}{\@nameuse{\string#1@A}}}
    \@namedef{\string#1@A}##1{\@nameuse{\string#1@B}[##1]{##1}}
    \@namedef{\string#1@B}[##1]##2{%
        \escapechar`\@ \relax
        \@namedef{theshort\string#1}{##1}
        \@namedef{the\string#1}{##2}
        \escapechar=92
        }
    }

% \newlongfield@AFM defines a long-macro also called '\#1', which also defines a long-macro called '\the@#1'.
\def\newlongfield@AFM#1{%
    \long\def#1##1{%
        \escapechar`\@ \relax
    	\long\@namedef{the\string#1}{##1}
    	\escapechar=92
        }
    }
%%% AUXILIARY MACROS %%%




%%%%% FIRST AND LAST PAGES %%%
\newcounter{firstpage@AFM}
\setcounter{firstpage@AFM}{0}

\def\firstpage #1{\setcounter{firstpage@AFM}{#1}\relax}
\setcounter{page}{\thefirstpage@AFM\relax}

\def \lastpage@AFM{\pageref*{LastPage}}

\AtBeginDocument{%
    % Print first page info
	\setcounter{page}{\thefirstpage@AFM\relax}
	\thispagestyle{first}
	\makepapertitle@AFM
    \mynewp@ge
    }

\let\mynewp@ge\newpage

\AtEndDocument{%
    % Fix Bibtex style
%    \bibliographystyle{abbrv}
    % Print editorial info
%    \PrintEditInfo
    % Label at the last page in order to count the number of pages
    \label{LastPage}
    }
%%% End FIRST AND LAST PAGES %%%

%%%%% TITLE PAGE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\narrowpar@AFM#1#2{%
    \begingroup
        \parindent1cm \narrower%
        \small \noindent%
        {\sffamily\bfseries#1.}
        \parindent15pt%
        \rm#2\par
    \endgroup
    \vskip24pt
   }

\def\footnote@AFMsp#1#2{%
    \def\@thefnmark{}%
    \ifx\relax#2\relax
        \relax%
    \else
%        \begin{NoHyper}
            \@footnotetext{\textit{#1}#2}%
%        \end{NoHyper}
    \fi
    }

\def\footnote@AFM#1#2{%
    \def\@thefnmark{}%
    \ifx\relax#2\relax
        \relax%
    \else
%        \begin{NoHyper}
            \@footnotetext{\textit{#1:}\enskip#2}%
%        \end{NoHyper}
    \fi
    }


%%% Metadata %%%
\newfield@AFM\JournalName  \JournalName{Annals of Formalized Mathematics}
\newfield@AFM\YEAR  \YEAR{\the\year{}}
\newfield@AFM\NUMBER  \NUMBER{{\color{red}n}}
\newfield@AFM\VOLUME  \VOLUME{{\color{red}v}}
\newfield@AFM\ISSNprint  \ISSNprint{1804-1388}
\newfield@AFM\ISSNonline  \ISSNonline{2336-1298}
\newfield@AFM\DOIName  \DOIName{DOI}
\newfield@AFM\DOI  \DOI{{\color{red}\url{https://doi.org/XXX}}}
\newfield@AFM*\author  \author{\firstname \middlename \lastname}
\newfield@AFM*\title  \title{Title of the paper}
\newfield@AFM\AbstractName  \AbstractName{Abstract}
\RenewDocumentEnvironment{abstract}{+b}{\gdef\theabstract{#1}}{}
\newfield@AFM\MscName  \MscName{MSC 2020}
\newfield@AFM\msc  \msc{AMS classification}
\newfield@AFM\KeywordsName  \KeywordsName{Keywords}
\newfield@AFM\keywords  \keywords{key words and phrases}
\newlongfield@AFM\contactinfo  \contactinfo{}
% \newfield@AFM\ContactInfoName  \ContactInfoName{Contact information}
\newfield@AFM\AffiliationName  \AffiliationName{Contact information}
\newfield@AFM\EmailName  \EmailName{Email}


\def\makepapertitle@AFM{
\noindent\begin{minipage}{\linewidth}
\noindent
\begin{tabularx}{\textwidth}{X X}
\begin{minipage}[c][2cm][c]{\linewidth}
\raggedright
    \raggedright
    \footnotesize
    \textbf{Preprint}
    % \the@JournalName \\
    % Volume \textbf{\the@VOLUME}\ (\the@YEAR), \thefirstpage@AFM--\lastpage@AFM \\
    % \the@DOIName:~\url{\the@DOI}
            %
\end{minipage}
&
\begin{minipage}[c][2cm][c]{\linewidth}
%\includegraphics[width=\linewidth, clip=true, trim = 290 160 290 150]{AFM.jpg}
\end{minipage}
\end{tabularx}

    \vspace*{5pt}
	\par\noindent{\color{secondaire}\rule{\textwidth}{0.5pt}}\\


	\vspace*{5pt}
    % Title
    {\begingroup
    \raggedright
    \baselineskip38pt \lineskiplimit6pt
    \noindent
    \color{tertiaire}
    \Large\textbf{\textsf{\the@title}}\par\endgroup}
    % Authors' names
    \ifx\relax\the@author\relax
        \relax%
    \else
        \begingroup
            \vskip20pt
            \baselineskip10pt%
            \noindent%
            \raggedright%
             \textit{\the@author}%
            \vskip24pt%
        \endgroup
    \fi
    % Abstract
\narrowpar@AFM{\color{tertiaire}\the@AbstractName}\theabstract
\end{minipage}

\vfill

% \footnote@AFMsp{}{\textcopyright~\the@YEAR\ \theshort@author }
% \footnote@AFMsp{}{This is an open access article licensed under the CC BY 4.0.}
% \footnote@AFMsp{}{To view a copy of the license, visit \url{https://creativecommons.org/licenses/by/4.0/}.}%
%     \footnote@AFM{\the@MscName}{\the@msc}
     \footnote@AFM{\the@KeywordsName}{\the@keywords}
%     \footnote@AFMsp{}{ }
     \footnote@AFM{\the@AffiliationName}{\the@contactinfo}

%     \footnote@AFMsp{}{\the@support}
%     \footnote@AFMsp{}{\emph{Received:} \the@receiveddate}
%     \footnote@AFMsp{}{\emph{Final form:} \the@finaldate}
%     \footnote@AFMsp{}{\emph{Accepted:} \the@accepteddate}
    }
%%% End metadata %%%


%%%%% TITLE PAGE INFO %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% This is the macro that will actually be used in the main tex file.  It
% calls \authorsname, if the (optional) author's name is present; and calls
% addresses, otherwise (when there is only one author).
\def \authorinfo{\@ifnextchar[{\authorsname}{\addresses}}

% Each time that this macro is called, it adds the info entered (author's
% name (#1), address (#2) and email (#3)) to \the@contactinfo.
\def \authorsname[#1]#2#3{%
    \g@addto@macro\the@contactinfo{%
        \par\noindent%
        \begingroup%
            \footnotesize%
            \interlinepenalty10000%
            \leftskip 3em%
            \rightskip 2em plus 8em%
            #1:
            \ifx\relax#2\relax
                \texttt{\href{mailto:#3}{#3}} \par
            \else
                #2. \texttt{\href{mailto:#3}{#3}}\par
            \fi
        \endgroup
        }
    }

% Each time that this macro is called, it adds the info entered (author's
% address (#1) and email (#2)) to \the@contactinfo.
\def \addresses#1#2{%
    \g@addto@macro\the@contactinfo{%
        \par\noindent
        \begingroup
            \footnotesize%
            \interlinepenalty10000%
            \leftskip 3em%
            \rightskip 2em plus 8em%
            \ifx\relax#1\relax
                \textit{\the@EmailName:} \texttt{#2}.\par
            \else
                \textit{\the@AffiliationName:} #1.\par\noindent%
                \textit{\the@EmailName:} \texttt{#2}.\par
            \fi
        \endgroup
        }
    }
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%% Theorem and proof %%%
\newfield@AFM\support \support{\relax}



\newfield@AFM\ConjectureName  \ConjectureName{Conjecture}
\newfield@AFM\CorollaryName  \CorollaryName{Corollary}
\newfield@AFM\DefinitionName  \DefinitionName{Definition}
\newfield@AFM\ExampleName  \ExampleName{Example}
\newfield@AFM\LemmaName  \LemmaName{Lemma}
\newfield@AFM\SubLemmaName  \SubLemmaName{Sublemma}
\newfield@AFM\ProblemName  \ProblemName{Problem}
\newfield@AFM\ProofName  \ProofName{Proof}
\newfield@AFM\PropositionName  \PropositionName{Proposition}
\newfield@AFM\RemarkName  \RemarkName{Remark}
\newfield@AFM\TheoremName  \TheoremName{Theorem}
\newfield@AFM\NotationName  \NotationName{Notation}
%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newfield@AFM\ExamplesName  \ExamplesName{Examples}
\newfield@AFM\RemarksName  \RemarksName{Remarks}

\def\equalenv#1#2{%
\@ifundefined{#1}%
{\newenvironment{#1}{\begin{#2}}{\end{#2}}}%
{\ClassWarningNoLine{AFM}{%
 #1 already defined: I won't redefine it!}}}


\newtheoremstyle{AFMdefinition}
	{1em} % space above the theorem
	{1ex} % space below the theorem
	{\itshape} % name of the body font
	{} % space to indent
	{\bfseries\itshape\sffamily} % name of head font
	{.} % punctuation between head and body
	{ } % space after theorem head
	{}

\theoremstyle{AFMdefinition}
\newtheorem{definition}{\the@DefinitionName}[section]
\newtheorem{notation}[definition]{\the@NotationName}

\newtheoremstyle{AFM}
	{1em} % space above the theorem
	{1ex} % space below the theorem
	{\itshape} % name of the body font
	{} % space to indent
	{\bfseries\sffamily} % name of head font
	{.} % punctuation between head and body
	{ } % space after theorem head
	{}

\theoremstyle{AFMplain}
\newtheorem{theorem}[definition]{\the@TheoremName}
\newtheorem{lemma}[definition]{\the@LemmaName}
\newtheorem{sublemma}[definition]{\the@SubLemmaName}
\newtheorem{proposition}[definition]{\the@PropositionName}
\newtheorem{corollary}[definition]{\the@CorollaryName}
\newtheorem{conjecture}[definition]{\the@ConjectureName}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newtheoremstyle{AFMremark}
	{1em} % space above the theorem
	{1ex} % space below the theorem
	{} % name of the body font
	{} % space to indent
	{\sffamily\itshape} % name of head font
	{.} % punctuation between head and body
	{ } % space after theorem head
	{}

\theoremstyle{AFMremark}
\newtheorem{remark}[definition]{\the@RemarkName}
\newtheorem{example}[definition]{\the@ExampleName}
\newtheorem{remarks}[definition]{\the@RemarksName}
\newtheorem{examples}[definition]{\the@ExamplesName}
%%%%% End theorem and proof %%%

%%% widows and orphans horizontal overruns management
\widowpenalty1000000
\clubpenalty1000000
\overfullrule=6pt
%%% end widows and orphans horizontal overruns management



%%%%% SECTIONS, SUBSECTIONS, ... %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\sectionfont{\raggedright\sffamily\bfseries\mathversion{bold}\large\textcolor{secondaire}}

\def\subsectionfont{\raggedright\sffamily\bfseries\mathversion{bold}\textcolor{secondaire}}

\def\subsubsectionfont{\raggedright\sffamily\bfseries\fontshape{it}\selectfont\mathversion{bold}\textcolor{secondaire}}


\def\section{\@startsection{section}{1}{\z@}
  {2em \@plus 1em \@minus 1em}{1em \@plus 1ex \@minus 1ex}
  {\sectionfont}}

\def\subsection{\@startsection{subsection}{2}{\z@}
  {1em \@plus 1ex \@minus 1ex}{1ex \@plus 0.5ex \@minus 0.5ex}
 {\subsectionfont}}

\def\subsubsection{\@startsection{subsubsection}{3}{\z@}
  {-2ex \@plus -2ex \@minus -0.2ex}{0.5ex \@plus 0.2ex}
  {\subsubsectionfont}}

\def\paragraph{\@startsection{paragraph}{4}{\z@}
  {3.25ex\@plus1ex\@minus.2ex}{-.5em}
  {\sffamily\bfseries\mathversion{bold}\textcolor{secondaire}}}

\def\subparagraph{\@startsection{subparagraph}{5}
  {\parindent}{3.25ex\@plus1ex\@minus .2ex}{-.5em}
  {\normalfont\normalsize\sffamily\bfseries\mathversion{bold}\textcolor{secondaire}}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%% EDITORIAL INFO %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newfield@AFM\receiveddate    \receiveddate{{\color{red}Received date}}
\newfield@AFM\finaldate    \finaldate{{\color{red}Final date}}
\newfield@AFM\accepteddate    \accepteddate{{\color{red}Accepted date}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\endinput
