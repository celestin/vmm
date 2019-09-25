/*********************************************************************
 *    Copyright 2004-2009 Synopsys, Inc.
 *    All Rights Reserved Worldwide
 *
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

`ifndef VMM_OBJECT__SV
`define VMM_OBJECT__SV

`ifndef VMM_OBJECT
   `define VMM_OBJECT                 vmm_object
`endif
`ifndef VMM_OBJECT_NEW_ARGS
   `define VMM_OBJECT_NEW_ARGS
   `define VMM_OBJECT_NEW_EXTERN_ARGS
   `define VMM_OBJECT_NEW_CALL
`endif
`ifndef VMM_OBJECT_BASE_NEW_ARGS
   `define VMM_OBJECT_BASE_NEW_ARGS
   `define VMM_OBJECT_BASE_NEW_EXTERN_ARGS
`endif
`ifdef VMM_OBJECT_BASE
   `ifndef VMM_OBJECT_BASE_NEW_CALL
      `define VMM_OBJECT_BASE_NEW_CALL
   `endif
`endif
`ifndef VMM_OBJECT_BASE_METHODS
   `define VMM_OBJECT_BASE_METHODS
`endif

typedef class `VMM_OBJECT;
`ifdef VMM_OBJECT_BASE
typedef class `VMM_OBJECT_BASE;
`endif

//---------------------------------------------------------------------
// vmm_object
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
virtual class vmm_object
`ifdef VMM_OBJECT_BASE
   extends `VMM_OBJECT_BASE
`endif
;

   typedef enum {VMM_UNKNOWN, VMM_OBJECT, VMM_DATA, VMM_SCENARIO,
		 VMM_MS_SCENARIO, VMM_CHANNEL, VMM_NOTIFY,
                 VMM_XACTOR, VMM_SUBENV, VMM_ENV,
                 VMM_CONSENSUS, VMM_TEST} type_e;
   
   typedef enum {IN_BY_DEFAULT, OUT_BY_DEFAULT} namespace_typ_e;
   
   //----------------------
   // variables
   //----------------------
   static local vmm_log log = new("Global", "default");
   
   local string name;
   local type_e typ;
   
   local vmm_object _parent;
   local vmm_object children[$];
   local int next_child = 0;
   
   local static vmm_object registered_objects[$];
   local static vmm_object roots[$];
   local static int next_root  = 0;
   
   local static namespace_typ_e namespace_type[string];
   local string name_in_namespace[string];
   
   local bit implicit_phasing_enabled = 1;

   
   //----------------------
   // methods
   //----------------------

`ifdef VMM_OBJECT_BASE_METHODS
   `VMM_OBJECT_BASE_METHODS
`endif

   //------------------------
   // VMM1.1 functions
   //------------------------
   
   extern function new(vmm_object parent = null
                       `VMM_OBJECT_BASE_NEW_ARGS);
   extern function void       set_parent(vmm_object parent);
   extern function vmm_object get_parent(type_e typ = VMM_OBJECT);
   extern function type_e     get_type();
   extern function string     get_hier_inst_name();
   extern local function vmm_log get_child_log(vmm_object child);
   extern local function vmm_log get_parent_log(vmm_object parent);


   //-----------------------------
   // VMM1.2 functions
   //-----------------------------
   
   //--------
   // public
   //--------
   //pure  virtual  function string get_typename();   //implementation should be left empty
   extern         function void       set_object_name(string name, string space = "");                         
   extern virtual function void       set_parent_object(vmm_object parent);
   
   extern         function vmm_object get_parent_object(string space = "");
   extern         function vmm_object get_root_object(string space = "");
   extern         function int        get_num_children();
   extern         function vmm_object get_nth_child(int n);
   extern         function bit        is_parent_of(vmm_object obj, string space = "");
   
   extern         function string     get_object_name(string space = "");
   extern         function string     get_object_hiername(vmm_object root = null, string space = "");
   
   extern         function vmm_object find_child_by_name(string name, string space = "");
   extern static  function vmm_object find_object_by_name(string name, string space = "");
   
   extern static  function int        get_num_roots(string space =  "");
   extern static  function vmm_object get_nth_root(int n, string space = "");
   
   extern virtual function vmm_log    get_log();
   extern virtual function void       kill_object();
   
   extern         function void       display(string prefix = "");
   extern virtual function string     psdisplay(string prefix = "");
   
   extern static  function void       print_hierarchy(vmm_object root = null);
   
   extern virtual function void       implicit_phasing(bit is_on);
   extern virtual function bit        is_implicitly_phased();
   
   extern static  function bit        create_namespace(string name, namespace_typ_e typ = OUT_BY_DEFAULT);
   extern static  function void       get_namespaces(output string names[]);
   extern         function bit        is_in_namespace(string space);
   
   //--------
   // local
   //--------
   
   extern local function void    print_tree(int level = 0);
   
endclass: vmm_object

//------------------------
// VMM1.1 implementation
//------------------------

//function vmm_object::new(vmm_object parent
//                         `VMM_OBJECT_BASE_NEW_ARGS);
//   this.typ = VMM_UNKNOWN; // Find out type only if needed
//   this.set_parent(parent);
//endfunction


function void vmm_object::set_parent(vmm_object parent);
   vmm_log par;
   vmm_log log = null;

   if (parent == null && this._parent != null) begin
      // Break the existing parent/child relationship
      par = this.get_parent_log(this._parent);
      log = this.get_child_log(this);
      if (par != null && log != null) par.is_not_above(log);
   end

   this._parent = parent;
   if (parent == null) return;

   // If both this and the parent have a vmm_log instance
   // make this log below the parent's log
   par = this.get_parent_log(this._parent);
   if (log == null) log = this.get_child_log(this);
   if (par != null && log != null) par.is_above(log);
endfunction


function vmm_log vmm_object::get_child_log(vmm_object child);
   // Note: only SOME of the VMM objects have their own log instances
   begin
      vmm_channel obj;
      if ($cast(obj, child)) begin
         // If is a shared instance, abort
         if (obj.log.get_instance() == "[shared]") return null;
         return obj.log;
      end
   end
   begin
      vmm_xactor obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
   begin
      vmm_consensus obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, child)) begin
         return obj.log;
      end
   end
`endif

  return null;
endfunction: get_child_log


function vmm_log vmm_object::get_parent_log(vmm_object parent);
   // Only some kind of objects can be hierarhical parents
   begin
      vmm_xactor obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, parent)) begin
         return obj.log;
      end
   end
`endif

   // if the parent is unsuitable, nothing to do
   return null;
endfunction: get_parent_log


function vmm_object vmm_object::get_parent(type_e typ);
   vmm_object obj = this;

   while (obj._parent != null) begin
      if (typ == VMM_OBJECT ||
          obj._parent.get_type() == typ) return obj._parent;

      obj = obj._parent;
   end
   return null;
endfunction


function vmm_object::type_e vmm_object::get_type();
   if (this.typ != VMM_UNKNOWN) return this.typ;

   // Find out -- and cache -- the object type
   begin
      vmm_scenario obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_SCENARIO;
         return this.typ;
      end
   end
   begin
      vmm_data obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_DATA;
         return this.typ;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_ms_scenario obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_MS_SCENARIO;
         return this.typ;
      end
   end
`endif
   begin
      vmm_channel obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_CHANNEL;
         return this.typ;
      end
   end
   begin
      vmm_notify obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_NOTIFY;
         return this.typ;
      end
   end
   begin
      vmm_xactor obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_XACTOR;
         return this.typ;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_SUBENV;
         return this.typ;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_ENV;
         return this.typ;
      end
   end
   begin
      vmm_consensus obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_CONSENSUS;
         return this.typ;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, this)) begin
         this.typ = VMM_TEST;
         return this.typ;
      end
   end
`endif

   // I give up!
   this.typ = VMM_OBJECT;
   return this.typ;
endfunction


function string vmm_object::get_hier_inst_name();
   vmm_xactor xact;
   vmm_subenv sub;
   vmm_env    env;
   vmm_log    log;
   string     name;

   log  = null;
   name = "[unknown]";

   case (this.get_type())

   VMM_DATA:        name = "[vmm_data]";
   VMM_SCENARIO:    name = "[vmm_scenario]";
   VMM_MS_SCENARIO: name = "[vmm_ms_scenario]";
   VMM_NOTIFY:      name = "[vmm_notify]";

   VMM_CHANNEL:     begin
      vmm_channel obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_XACTOR: begin
      vmm_xactor obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_SUBENV: begin
      vmm_subenv obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_ENV: begin
      vmm_env obj;
      $cast(obj, this);
      log = obj.log;
   end

   VMM_CONSENSUS: begin
      vmm_consensus obj;
      $cast(obj, this);
      log = obj.log;
   end

`ifdef NOT_YET_IMPLEMENTED
   VMM_TEST: begin
      vmm_test obj;
      $cast(obj, this);
      log = obj.log;
   end
`endif
   endcase

   // Unamed object?
   if (log == null) begin
      if (this._parent == null) return name;
      return {this._parent.get_hier_inst_name(), ".", name};
   end

   name = log.get_instance();

   // If named using hierarchical names, that's it!
   if (log.uses_hier_inst_name()) return name;

   // If the log instance does not have an instance name...
   if (name == "") name = log.get_name();
   if (name == "") name = "[Anonymous]";

   // If no parent, that's it.
   if (this._parent == null) return name;

   return {this._parent.get_hier_inst_name(), ".", name};
endfunction

//------------------------
// VMM1.2 implementation
//------------------------

//-----------
// public
//-----------
function vmm_object::new(vmm_object parent
                         `VMM_OBJECT_BASE_NEW_ARGS);
      string space;
      bit ok;
      
      this.name = name;
      //if (name == "") `vmm_warning(this.log, "Object has no name. Please specify a name for the object");
      if (parent == this) begin
            `vmm_fatal(this.log,`vmm_sformatf("Object %s is setting itself as its parent!",  name));
            return;
      end
      else this._parent = parent;
      if (this._parent != null) this._parent.children.push_back(this);
      if (this._parent == null) this.roots.push_back(this);
      registered_objects.push_back(this);
      
      ok = namespace_type.first(space);
      while(ok) begin
         if (namespace_type[space] == IN_BY_DEFAULT) this.name_in_namespace[space] = this.name;
         else if (namespace_type[space] == OUT_BY_DEFAULT) this.name_in_namespace[space] = "";
         ok = namespace_type.next(space);
      end
      
   endfunction:new
                            
   function void       vmm_object::set_object_name(string name, string space = ""); 
      if (space == "") begin
        this.name = name;
        if (name == "") `vmm_warning(this.log, "Object has no name in default namespace. Please specify a name for the object");
      end
      else begin
         if (namespace_type.exists(space)) this.name_in_namespace[space] = name;
         else `vmm_warning(this.log, `vmm_sformatf("Namespace /%s/ does not exists.", space));
      end
   endfunction:set_object_name
   
   function void       vmm_object::set_parent_object(vmm_object parent);
      
      if (this._parent == parent) return;  //nothing changed
      
      if (this._parent == null && parent != null) begin   //add parent
         if (this.is_parent_of(parent)) begin
            `vmm_fatal(this.log, `vmm_sformatf("Setting %s as parent of %s will form hierarchy cycle. Object hierarchies should be strict trees.", parent.get_object_name(), this.get_object_name()));
            return;
         end
         else this._parent = parent;
         foreach (vmm_object::roots[i]) begin
            if (vmm_object::roots[i] == this) begin
               vmm_object::roots.delete(i);
               break;
            end
         end
         this._parent.children.push_back(this);
         return;
      end
      
      if (this._parent != null && parent == null) begin    //remove parent
         this.roots.push_back(this);
         foreach (this._parent.children[i]) begin
            if (this._parent.children[i] == this) begin
               this._parent.children.delete(i);
               break;
            end
         end
         this._parent = parent;
         return;
      end
      
      if (this._parent != null && parent != null) begin    //replace parent
         if (this.is_parent_of(parent)) begin
            `vmm_fatal(this.log, `vmm_sformatf("Setting %s as parent of %s will form hierarchy cycle. Object hierarchies should be strict trees.", parent.get_object_name(), this.get_object_name()));
            return;
         end
         else begin
            foreach (this._parent.children[i]) begin
               if (this._parent.children[i] == this) begin
                  this._parent.children.delete(i);
                  break;
               end
            end
            this._parent = parent;
            this._parent.children.push_back(this);
         end
         return;
      end
   endfunction:set_parent_object
   
   function vmm_object vmm_object::get_parent_object(string space = "");
      vmm_object physical_parent;
      vmm_object return_parent;
      string tmp;
      
      if (space == "") return this._parent;
      if (this.is_in_namespace(space)) begin
         tmp = this.name_in_namespace[space];
         if (tmp[0] == "^") return null;  // if the name indicates it's root
         physical_parent = this._parent;
         if (physical_parent == null) return null;  //if physically it's root
         tmp = physical_parent.name_in_namespace[space];
         if (tmp == "^") return null;   //if its parent's name indicates it's root
         if (tmp == "") begin  //if parent is skipped
            physical_parent = physical_parent._parent;
            while (physical_parent != null) begin
               tmp = physical_parent.name_in_namespace[space];
               if (tmp != "" && tmp != "^") return physical_parent;
               if (tmp == "^") return null;
               if (tmp == "") begin
                  physical_parent = physical_parent._parent;
               end
            end
            return null;  //if all hierarchy up to root are skipped
         end
         return physical_parent;  //if parent is present
      end
      `vmm_error(this.log, "Namespace does not exist or Object is not in Namespace.");
      return null;
   endfunction:get_parent_object
   
   function vmm_object vmm_object::get_root_object(string space = "");
      vmm_object root;
      
      if ( this.is_in_namespace(space)) begin
         root = this;
         while (root.get_parent_object(space) != null) root = root.get_parent_object(space);
         return root;
      end
      `vmm_error(this.log, "Namespace does not exist or Object is not in Namespace.");
      return null;
   endfunction:get_root_object
   
   function int        vmm_object::get_num_children();
     return this.children.size();
   endfunction:get_num_children
   
   function vmm_object vmm_object::get_nth_child(int n);
      if (n < 0 || n >= this.children.size()) return null;
      return this.children[n];
   endfunction:get_nth_child
   
   function string     vmm_object::get_object_name(string space = "");
      string tmp;

      if (space == "") return this.name;
      else begin
         if (namespace_type.exists(space)) begin
            tmp = this.name_in_namespace[space];
            if (tmp[0] == "^") tmp = tmp.substr(1, tmp.len()-1);
            return tmp;
         end
         else begin
            `vmm_warning(this.log, `vmm_sformatf("Namespace /%s/ does not exists.", space));
            return "";
         end
      end
   endfunction:get_object_name
   
   function string     vmm_object::get_object_hiername(vmm_object root = null, string space = "");
      string hiername = "";
      vmm_object next_parent;
      
      next_parent = this;
      while (next_parent != null) begin
        if (next_parent == root) break;
        if (next_parent == this) hiername = next_parent.get_object_name(space);
        else hiername = {next_parent.get_object_name(space), ":", hiername};
        next_parent = next_parent.get_parent_object(space);
      end
      return hiername;
   endfunction:get_object_hiername
   
   function vmm_object vmm_object::find_child_by_name(string name, string space = "");
      string hiername;
      `vmm_path_compiled compiled_hiername;
      `vmm_path_regexp compiled_pattern;

      compiled_pattern = vmm_path_match::compile_pattern(name, log);

      foreach(registered_objects[i]) begin
         if (this.is_parent_of(registered_objects[i], space)) begin
            hiername = registered_objects[i].get_object_hiername(this, space);
            compiled_hiername = vmm_path_match::compile_path(log, this, hiername, space);
            if (vmm_path_match::match(compiled_hiername, compiled_pattern)) return registered_objects[i];
         end
      end
      return null;
   endfunction:find_child_by_name
           
   function vmm_object vmm_object::find_object_by_name(string name, string space = "");
      `vmm_path_compiled compiled_hiername;
      `vmm_path_regexp compiled_pattern;

      compiled_pattern = vmm_path_match::compile_pattern(name, log);

      foreach(registered_objects[i]) begin
         compiled_hiername = vmm_path_match::compile_path(log, registered_objects[i], "", space);
         if (vmm_path_match::match(compiled_hiername, compiled_pattern)) return registered_objects[i];
      end
      return null;
   endfunction:find_object_by_name
   
   function int        vmm_object::get_num_roots(string space = "");
      int root_count = 0;
      
      if (space == "") return vmm_object::roots.size();
      
      if (namespace_type.exists(space)) begin
         foreach (registered_objects[i]) begin
            if (registered_objects[i].name_in_namespace[space] != "" && 
                registered_objects[i].name_in_namespace[space] != "^" && 
                registered_objects[i].get_parent_object(space) == null) root_count++;
         end
         return root_count;
      end
      `vmm_error(log, "Namespace does not exist.");
      return 0;
   endfunction:get_num_roots
   
   function vmm_object vmm_object::get_nth_root(int n, string space = "");
      int num_roots;
      int root_count = 0;
      
      if (space == "") begin
         if (n < 0 || n >= roots.size()) return null;
         return roots[n];
      end
      
      if (namespace_type.exists(space)) begin
         num_roots = get_num_roots(space);
         if (n < 0 || n >= num_roots) return null;
         foreach (registered_objects[i]) begin
            if (registered_objects[i].name_in_namespace[space] != "" && 
                registered_objects[i].name_in_namespace[space] != "^" && 
                registered_objects[i].get_parent_object(space) == null) root_count++;
            if ( n == root_count - 1) return registered_objects[i];
         end
         return null;
      end
      `vmm_error(log, "Namespace does not exist.");
      return null;
   endfunction:get_nth_root
   
   function vmm_log    vmm_object::get_log();
      return vmm_object::log;
   endfunction:get_log
   
   function void       vmm_object::kill_object();
      
      foreach (this.registered_objects[i]) begin
         if (this.registered_objects[i] == this) begin
            this.registered_objects.delete(i);
            break;
         end
      end
      
      for (int j = 0; j < this.registered_objects.size(); j++) begin
         if (this.is_parent_of(this.registered_objects[j])) this.registered_objects.delete(j--);
      end

      if (this._parent == null) begin
         foreach (this.roots[i]) begin
            if (this.roots[i] == this) begin
               this.roots.delete(i);
               break;
            end
         end
      end

      if (this._parent != null) begin
         foreach (this._parent.children[i]) begin
            if (this._parent.children[i] == this)  begin
               this._parent.children.delete(i);
               break;
            end
         end
         this._parent = null;
      end
      
   endfunction:kill_object
   
   function void       vmm_object::display(string prefix = "");
      $display(this.psdisplay(prefix));
   endfunction :display
   
   function string     vmm_object::psdisplay(string prefix = "");
      $sformat(psdisplay, "%sObject \"%s\"",  prefix,this.get_object_hiername());
   endfunction:psdisplay
   
   function void       vmm_object::print_hierarchy(vmm_object root = null);
      if (root == null) begin
         foreach (roots[i]) begin
            print_hierarchy(roots[i]);
            $write("\n");
         end
         return;
      end
      
      root.print_tree(0);
   endfunction:print_hierarchy

   function void       vmm_object::implicit_phasing(bit is_on);
      this.implicit_phasing_enabled = is_on;
   endfunction:implicit_phasing
   
   function bit        vmm_object::is_implicitly_phased();
      return this.implicit_phasing_enabled;
   endfunction:is_implicitly_phased


   function bit        vmm_object::create_namespace(string name, namespace_typ_e typ = OUT_BY_DEFAULT);
      if (name ==  "") begin
         `vmm_error(log, "Namespace can not be named to empty string.");
         return 0;
      end
      
      if (namespace_type.exists(name)) begin
         `vmm_warning(log, `vmm_sformatf("Namespace \"%s\" already exists.", name));
         return 0;
      end
      
      namespace_type[name] = typ;
     
      foreach(registered_objects[i]) begin
         if (typ == IN_BY_DEFAULT) registered_objects[i].name_in_namespace[name] = registered_objects[i].name;
         else if (typ == OUT_BY_DEFAULT) registered_objects[i].name_in_namespace[name] = "";
      end
   endfunction:create_namespace
   
   function void       vmm_object::get_namespaces(output string names[]);
      string name;
      string tmp[];
      int i;
      bit ok;
      
      tmp = new[namespace_type.num()];
      i = 0;
      
      ok = namespace_type.first(name);
      while (ok) begin
         tmp[i++] = name;
         ok = namespace_type.next(name);
      end
      names = new [i] (tmp);
   endfunction:get_namespaces
   
   function bit        vmm_object::is_in_namespace(string space);
      return ( space == "" || (namespace_type.exists(space) && this.name_in_namespace[space] != "" && this.name_in_namespace[space] != "^") );
   endfunction:is_in_namespace

//----------
// local
//----------
   function bit    vmm_object::is_parent_of(vmm_object obj, string space = "");
      vmm_object next_parent;
      
      if (obj == null) return 0;
      else next_parent = obj;
      
      while (next_parent != null) begin
         next_parent = next_parent.get_parent_object(space);
         if (next_parent == this) return 1;
      end
      
      return 0;
      
   endfunction:is_parent_of
   
   function void    vmm_object::print_tree(int level = 0);
      int i;
      vmm_object child;

      if (level > 1) repeat (level-1) $write("|  ");
      if (level > 0) $write("|--");
      $write("[%s]\n", this.get_object_name());
      i = 0;
      child = this.get_nth_child(i++);
      while (child != null) begin
         child.print_tree(level+1);
         child = this.get_nth_child(i++);
      end

   endfunction:print_tree


//---------------
// macro
//---------------
`define vmm_typename(_name) \
   typedef _name my_typedef; \
   virtual function string get_typename(); \
      return $typename(this); \
   endfunction

`endif // VMM_OBJECT__SV
