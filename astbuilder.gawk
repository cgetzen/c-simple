#!/usr/bin/gawk -f

# fixme: need lick to parent node!

###############################

func dumperr(n,c) {
    if ( n > 0 ) {
        printf "Error in line %d, field %d: problem with \"%s\" (%s)\n",
            NR,n,$n,c > "/dev/stderr"
    } else {
        printf "Error: %s\n",c > "/dev/stderr"
    }
    errno = 1;
    exit(1);
}

func check_rule_line() {
    if ( match($1,/[[:alpha:]][[:alnum:]_]*(:[[:alpha:]][[:alnum:]_]*)?/)==0 \
         || RLENGTH!=length($1) ) {
        dumperr( 1, "left hand side should be ident or ident:ident" );
    }
    if ( match($2,/==>/)==0 || RLENGTH!=length($2) ) {
        dumperr( 2, "arrow should be ==>" );
    }
    for( i=3; i<=NF; i++ )
    {
        if ( match($i,/(\*?)[[:alpha:]][[:alnum:]_]*/)==0 \
             || RLENGTH!=length($i) ) {
            dumperr( i, "right hand identifier should be ident or *ident" );
        }
    }
}

func check_external_line() {
    if (    match($1,/[[:alpha:]][[:alnum:]_]*/)==0 \
         || RLENGTH!=length($1) ) {
        dumperr( 1, "left hand side should be ident" );
    }
    if ( match($2,/external/)==0 || RLENGTH!=length($2) ) {
        dumperr( 2, "should be \"external\"" );
    }
    if ( match($3,/[\"\<][[:alnum:]_\.]+[\"\>]/)==0 \
         || RLENGTH!=length($3) ) {
        dumperr( 3, "should be \"include.h\" or <include.h>" );
    }
    if ( NF > 3 ) {
        dumperr( 4, "there should only be 3 fields for an external line");
    }
}


func check_decwith_line() {
    if (    match($1,/[[:alpha:]][[:alnum:]_]*/)==0 \
         || RLENGTH!=length($1) ) {
        dumperr( 1, "left hand side should be ident" );
    }
    if ( match($2,/decwith/)==0 || RLENGTH!=length($2) ) {
        dumperr( 2, "should be \"decwith\"" );
    }
}


###############################

func get_abstract_name(kind) {
    return kind;
}

func get_abstractptr_name(kind) {
    return kind"_ptr";
}

func get_unionlist_name(kind) {
    return "u_"tolower(kind)"_list";
}

func get_unionmember_name(kind) {
    return "u_"tolower(kind);
}

func get_concrete_name(kind,instof) {
    if ( instof == "" ) return kind"Impl";
    else return instof;
}

func get_member_name(e,   n,i,u,my_u) {
    #reference to the e_th element of subclass_list
    u = 0;
    n = "m_" tolower(subclass_list[e]);
    for( i=1; i<=subclass_number; i++ )
    {
        if( subclass_list[i] == subclass_list[e] ) u++;
        if( i==e ) my_u = u;
    }

    if ( subclass_type[e] == "list" ) {
        if ( u>1 )  return n "_list_" my_u;
        else return n "_list";
    } else {
        if ( u>1 )  return n "_" my_u;
        else return n;
    }
}

###############################

func add_header() {

    Hheader = Hheader "#ifndef AST_HEADER\n"
    Hheader = Hheader "#define AST_HEADER\n"
    Hheader = Hheader "\n//Automatically Generated C++ Abstract Syntax Tree Interface\n\n";
    Hheader = Hheader "#include <list>\n";
    Hheader = Hheader "#include \"attribute.hpp\"\n";

    Cheader = Cheader "//Automatically Generated C++ Abstract Syntax Tree Class Hierarchy\n\n";
    Cheader = Cheader "#include <algorithm>\n";
    Cheader = Cheader "#include \"ast.hpp\"\n";
    Cheader = Cheader "extern int yylineno;\n";
}

func add_list(kind) {

    Hunion = Hunion "std::list<"get_abstractptr_name(kind)">* "get_unionlist_name(kind)";\n";

    Htypedef = Htypedef "typedef "get_abstract_name(kind)"* "get_abstractptr_name(kind)";\n"
}


func add_external( kind, f ) {

    Hforward = Hforward "class " get_abstract_name(kind)  ";\n";
    Hvisitor = Hvisitor "virtual void visit"get_abstract_name(kind) \
            "("get_abstract_name(kind)" *p) = 0;\n";

    Hunion = Hunion get_abstract_name(kind)"* "get_unionmember_name(kind)";\n";

    Cheader = Cheader "#include " f "\n";
}

func add_abstract( kind ) {

    Hforward = Hforward "class "get_abstract_name(kind)";\n";
    #Hvisitor = Hvisitor "virtual void visit"get_abstract_name(kind) \
    #       "("get_abstract_name(kind)" *p) = 0;\n";

    Hunion = Hunion get_abstract_name(kind)"* "get_unionmember_name(kind)";\n";

    Habstract = Habstract "class "get_abstract_name(kind)" : public Visitable {\n";
    Habstract = Habstract "public:\n";
    Habstract = Habstract "   Attribute m_attribute;\n";
    Habstract = Habstract "   Attribute* m_parent_attribute;\n";
    Habstract = Habstract "   virtual "get_abstract_name(kind) \
                " *clone() const = 0;\n";

    Habstract = Habstract "};\n\n";

}

func add_concrete( kind, instof,   c,i,m,t ) {

    c = get_concrete_name(kind,instof);

    Hforward = Hforward "class "c";\n";
    Hvisitor = Hvisitor "virtual void visit"c"("c" *p) = 0;\n";

    ###### Header stuff

    Hconcrete = Hconcrete "// "$0"\n";
    Hconcrete = Hconcrete "class "c" : public "get_abstract_name(kind)"\n";
    Hconcrete = Hconcrete "{\n";
    Hconcrete = Hconcrete "  public:\n";


    #----------
    Hconcrete = Hconcrete decarray[kind];

    #----------
    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            Hconcrete = Hconcrete "  std::list<"get_abstractptr_name(subclass_list[i])"> *"get_member_name(i)";\n";
        } else {
            Hconcrete = Hconcrete "  "get_abstract_name(subclass_list[i])" *"get_member_name(i)";\n";
        }
    }
    Hconcrete = Hconcrete "\n";

    #----------
    Hconcrete = Hconcrete "  "c"(const "c" &);\n"
    Hconcrete = Hconcrete "  "c" &operator=(const "c" &);\n";


    #----------
    Hconcrete = Hconcrete "  "c"(";
    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            Hconcrete = Hconcrete "std::list<"get_abstractptr_name(subclass_list[i])"> *p"i;
        } else {
            Hconcrete = Hconcrete get_abstract_name(subclass_list[i])" *p"i;
        }
        if (i!=subclass_number) { Hconcrete = Hconcrete ", "; }
    }
    Hconcrete = Hconcrete ");\n";


    #----------
    Hconcrete = Hconcrete "  ~"c"();\n";
    Hconcrete = Hconcrete "  virtual void visit_children( Visitor* v );\n";
    Hconcrete = Hconcrete "  virtual void accept(Visitor *v);\n";
    Hconcrete = Hconcrete "  virtual  "c"  *clone() const;\n";
    Hconcrete = Hconcrete "  void swap("c" &);\n";
    Hconcrete = Hconcrete "};\n\n";

    ####### Cpp stuff

    Cconcrete = Cconcrete "/********* "c" ************/\n";

    #FIXME: Get "clone" to work on the list types

    #---------- constructor
    Cconcrete = Cconcrete " "c"::"c"(";
    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            Cconcrete = Cconcrete "std::list<"get_abstractptr_name(subclass_list[i])"> *p"i;
        } else {
            Cconcrete = Cconcrete get_abstract_name(subclass_list[i])" *p"i;
        }
        if (i!=subclass_number) { Cconcrete = Cconcrete ", "; }
    }
    Cconcrete = Cconcrete ")  {\n";
    for( i=1; i<=subclass_number; i++ )
    {
        Cconcrete = Cconcrete "\t"get_member_name(i)" = p"i";\n";
    }
    Cconcrete = Cconcrete "\tm_attribute.lineno = yylineno;\n";
    Cconcrete = Cconcrete "\tm_parent_attribute = NULL;\n";

    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            t = get_abstractptr_name(subclass_list[i]);
            m = get_member_name(i);
            Cconcrete = Cconcrete "\tstd::list<"t">::iterator "m"_iter;\n";
            Cconcrete = Cconcrete "\tfor("m"_iter = "m"->begin();\n";
            Cconcrete = Cconcrete "\t  "m"_iter != "m"->end();\n";
            Cconcrete = Cconcrete "\t  ++"m"_iter){\n";
            Cconcrete = Cconcrete "\t\t(*"m"_iter)->m_parent_attribute = &m_attribute;\n";
            Cconcrete = Cconcrete "\t}\n";
        } else {
            Cconcrete = Cconcrete "\t"get_member_name(i)"->m_parent_attribute = &m_attribute;\n ";
        }
    }

    Cconcrete = Cconcrete " }\n";


    #---------- copy constructor
    Cconcrete = Cconcrete " "c"::"c"(const "c" & other) {\n";
    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            t = get_abstractptr_name(subclass_list[i]);
            m = get_member_name(i);
            Cconcrete = Cconcrete "\t"m" = new std::list<"t">;\n";
            Cconcrete = Cconcrete "\tstd::list<"t">::iterator "m"_iter;\n";
            Cconcrete = Cconcrete "\tfor("m"_iter = other."m"->begin();\n";
            Cconcrete = Cconcrete "\t  "m"_iter != other."m"->end();\n";
            Cconcrete = Cconcrete "\t  ++"m"_iter){\n";
            Cconcrete = Cconcrete "\t\t"m"->push_back( (*"m"_iter)->clone() );\n";
            Cconcrete = Cconcrete "\t}\n";
        } else {
            Cconcrete = Cconcrete "\t"get_member_name(i)" = other." \
                get_member_name(i)"->clone();\n";
        }
    }
    Cconcrete = Cconcrete " }\n";


    #---------- assignment op
    Cconcrete = Cconcrete " "c" &"c"::operator=(const "c" & other) { " \
            c" tmp(other); swap(tmp); return *this; }\n";


    #---------- swap
    Cconcrete = Cconcrete " void "c"::swap("c" & other) {\n";
    for( i=1; i<=subclass_number; i++ )
    {
        Cconcrete = Cconcrete "\tstd::swap("get_member_name(i)", other." \
            get_member_name(i)");\n";
    }
    Cconcrete = Cconcrete " }\n";


    #---------- destructor
    Cconcrete = Cconcrete " "c"::~"c"() {\n ";
    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            t = get_abstractptr_name(subclass_list[i]);
            m = get_member_name(i);
            Cconcrete = Cconcrete "\tstd::list<"t">::iterator "m"_iter;\n";
            Cconcrete = Cconcrete "\tfor("m"_iter = "m"->begin();\n";
            Cconcrete = Cconcrete "\t  "m"_iter != "m"->end();\n";
            Cconcrete = Cconcrete "\t  ++"m"_iter){\n";
            Cconcrete = Cconcrete "\t\tdelete( *"m"_iter );\n";
            Cconcrete = Cconcrete "\t}\n";
        } else {
            Cconcrete = Cconcrete "\tdelete("get_member_name(i)");\n ";
        }
    }
    Cconcrete = Cconcrete " }\n";

    #---------- visit_children
    Cconcrete = Cconcrete " void "c"::visit_children( Visitor* v ) {\n ";
    for( i=1; i<=subclass_number; i++ )
    {
        if ( subclass_type[i] == "list" ) {
            t = get_abstractptr_name(subclass_list[i]);
            m = get_member_name(i);
            Cconcrete = Cconcrete "\tstd::list<"t">::iterator "m"_iter;\n";
            Cconcrete = Cconcrete "\tfor("m"_iter = "m"->begin();\n";
            Cconcrete = Cconcrete "\t  "m"_iter != "m"->end();\n";
            Cconcrete = Cconcrete "\t  ++"m"_iter){\n";
            Cconcrete = Cconcrete "\t\t(*"m"_iter)->accept( v );\n";
            Cconcrete = Cconcrete "\t}\n";
        } else {
            Cconcrete = Cconcrete "\t"get_member_name(i)"->accept( v );\n ";
        }
    }
    Cconcrete = Cconcrete " }\n";


    #---------- clone and visit
    Cconcrete = Cconcrete " void "c"::accept(Visitor *v) { v->visit"c"(this); }\n";
    Cconcrete = Cconcrete " "c" *"c"::clone() const { return new "c"(*this); }\n";
    Cconcrete = Cconcrete " \n";
    Cconcrete = Cconcrete " \n";
}

###############################

func print_all_cpp() {

    print Cheader > outfile;
    print "\n" >> outfile;
    print Cconcrete >> outfile;
}

func print_all_h() {

    print Hheader > outfile;


    print "\n/********** Forward Declarations **********/\n" >> outfile;
    print Hforward >> outfile;

    print "\n/********** Pointer Typedefs **********/\n" >> outfile;
    print "typedef "startsymbol"* "startsymbol"_ptr;\n" >> outfile;
    print Htypedef >> outfile;

    print "\n/********** Union Type (from parse) **********/\n" >> outfile;
    print "#ifdef YYSTYPE_IS_TRIVIAL" >> outfile;
    print "#error Make sure to include this file _before_ parser.hpp" >> outfile;
    print "#endif" >> outfile;

    print "typedef union" >> outfile;
    print "{" >> outfile;
    print Hunion >> outfile;
    print "// a couple of hardcoded types" >> outfile;
    print "char* u_base_charptr;" >> outfile;
    print "int u_base_int;" >> outfile;
    print "} classunion_stype;" >> outfile;
    print "#define YYSTYPE classunion_stype" >> outfile;

    print "\n/********** Visitor Interfaces **********/\n" >> outfile;
    print "class Visitor{" >> outfile;
    print" public:" >> outfile;
    print"  virtual ~Visitor() {}" >> outfile;
    print Hvisitor >> outfile;
    print "};\n" >> outfile;

    print "class Visitable" >> outfile;
    print "{" >> outfile;
    print " public:" >> outfile;
    print "  virtual ~Visitable() {}" >> outfile;
    print "  virtual void visit_children(Visitor *v) = 0;" >> outfile;
    print "  virtual void accept(Visitor *v) = 0;" >> outfile;
    print "};\n" >> outfile;

    print "\n/********** Abstract Syntax Classes **********/\n" >> outfile;
    print Habstract >> outfile;
    print Hconcrete >> outfile;

    print "\n" >> outfile;
    print "#endif //AST_HEADER\n" >> outfile;
}

###############################

BEGIN {
    R = 0;
    validoutput["hpp"] = 1;
    validoutput["cpp"] = 1;
    if( !(outtype in validoutput) ) {
        dumperr( 0, "must be called with \"-v outtype=type where type is"\
                " one of the following: hpp, cpp" );
    }

    if( outfile=="" ) {
        dumperr( 0, "must be called with \"-v outfile=name where name is"\
                " is a valid output file name " );
    }
    startsymbol = "Program";
    add_header();
}

#eat the comments
(/#/) { $0 = substr($0,1,index($0,"#")-1);}

{ is_match = 0; }

(NF>0 && $2=="==>") {

      is_match = 1;

      check_rule_line();
      split($1,a,":");
      kind = a[1]; instof = a[2];

      delete subclass_list; delete subclass_type;
      subclass_number = NF-2;
      for( i=3; i<=NF; i++ )
      {
        if( index($i,"*") == 1 ) {
          this_subclass_list = substr($i,2);
          this_subclass_type = "list";
        } else {
          this_subclass_list = $i;
          this_subclass_type = "single";
        }

        alreadyuse[this_subclass_list] = 1;

        if( this_subclass_type == "list") {
            if ( !(this_subclass_list in alreadylist) ) {
                add_list(this_subclass_list);
            }
            alreadylist[this_subclass_list] = 1;
        }

        subclass_list[i-2] = this_subclass_list;
        subclass_type[i-2] = this_subclass_type;
      }

      #TODO: check this error handling

      if ( instof != "" ) {
        if ( !( instof in alreadyinst ) ) {
            add_concrete(kind,instof)
            alreadyinst[instof] = 1;
            } else {
            dumperr(1,"The CDEF instance \"" instof "\" has been declared twice");
            }
      } else {
        if ( !( kind in alreadyinst ) ) {
            add_concrete(kind,instof)
            alreadyinst[kind] = 1;
            } else {
            dumperr(1,"The CDEF kind \"" instof "\" has already been used as an instof");
            }
      }

      if ( !( kind in alreadydef ) ) {
        add_abstract(kind)
        alreadydef[kind] = 1;
      } else if (instof==""){
        dumperr(1,"The CDEF symbol \"" kind "\" has already been used as a instof");
      }
}

(NF>0 && $2=="external") {
    is_match = 1;

    check_external_line();
    kind = $1;
    f = $3;
    alreadydef[kind] = 1;

    add_external( kind, f );

}

#(NF>0 && $2=="decwith") {
#   is_match = 1;
#
#   check_decwith_line();
#   kind = $1;
#
#   if( kind in alreadydef ) {
#       dumperr(1,"The CDEF symbol \""kind"\" needs to have decwiths added before it is defined");
#   }
#
#   decoration = substr( $0, index($0,"decwith") + 8 );
#   decarray[kind] = decarray[kind] decoration ";\n"
#}

(NF>0 && is_match==0) {
    dumperr(2,"should be either \"==>\" or \"external\"");
}

END {

    for( i in decarray ) {
        if (! (i in alreadydef) ) {
            dumperr(0,"A decoration was put on \"" i "\" which is not defined");
        }
    }

    if ( errno == "" ) {
      for( i in alreadydef) {
        if ( (!(i in alreadyuse)) && (i != startsymbol )) {
            dumperr(0,"The CDEF symbol \"" i "\" was defined but not used");
        }
      }

      for( i in alreadyuse ) {
        if ( ! (i in alreadydef) ) {
            dumperr(0,"The CDEF symbol \"" i "\" was used but not defined");
        }
      }

      if ( outtype == "cpp" ) {
        print_all_cpp();
      } else if ( outtype == "hpp") {
        print_all_h();
      }
    }
}


