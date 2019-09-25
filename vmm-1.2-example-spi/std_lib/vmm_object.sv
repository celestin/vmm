//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

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

`ifndef NO_VMM12_PHASING
typedef class vmm_phase_def;
`endif

//---------------------------------------------------------------------
// vmm_object
//
`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
//
// Class: vmm_object
//   The vmm_object class is a virtual class that is used as the common base class 
//   for all VMM related classes. This helps to provide parent or child relationships for class instances. 
//
//   Additionally, it provides local, relative, and absolute hierarchical naming.              
                    
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
   static bit do_object_thresh_check = vmm_opts::get_bit("object_thresh_check", "Gloabal setting for checking object threshhold in object hierarchy, channel and scoreboard");
   static int children_thresh = vmm_opts::get_int("object_children_thresh", 100, "GLOBAL option that sets the number of child objects threshold");
   static int root_thresh = vmm_opts::get_int("object_root_thresh", 1000, "GLOBAL option that sets the number of root objects threshold");
   
   local string name;
   
   protected vmm_object _parent;
   local vmm_object children[$];
   
   local static vmm_object registered_objects[$];
   local static vmm_object roots[$];
   local static int next_root  = 0;
   
   local static namespace_typ_e namespace_type[string];
   local string name_in_namespace[string];
   
   local bit implicit_phasing_enabled = 1;
   local bit disable_hier_insert = 0;

   
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
   extern  virtual  function void       set_object_name(string name, string space = "");                         
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
   
   extern static  function void       print_hierarchy(vmm_object root = null, bit verbose = 0);
   
   extern virtual function void       implicit_phasing(bit is_on);
   extern virtual function bit        is_implicitly_phased();
   
   extern static  function bit        create_namespace(string name, namespace_typ_e typ = OUT_BY_DEFAULT);
   extern static  function void       get_namespaces(output string names[]);
   extern         function bit        is_in_namespace(string space);
   extern static  function void       register_object(vmm_object obj);
   extern static  function void       unregister_object(vmm_object obj);

   
   //--------
   // local
   //--------
   
   extern local function void    print_tree(int level = 0, bit verbose = 0);
   
endclass: vmm_object

//------------------------
// VMM1.1 implementation
//------------------------

// //////////////////////////////////////////// 
// Function: set_parent 
// 
// Specifies a new parent object to this object. Specifying a null parent, breaks any current
// parent or child relationship. An object may contain only one parent, but the identity
// of a parent can be changed dynamically. 
// 
//|   class C extends vmm_object;
//|      function new(string name, vmm_object parent=null);
//|         super.new (parent,name);
//|      endfunction
//|   endclass
//|   class D extends vmm_object;
//|      C c1;
//|      function new(string name, vmm_object  parent=null);
//|         super.new (parent,name);
//|         c1 = new ("c1",this);
//|      endfunction
//|   endclass
//|   
//|   initial begin 
//|      D d1 = new ("d1");
//|      D d2 = new ("d2");
//|      d1.c1.set_parent_object (d2);
//|   end
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


// //////////////////////////////////////////// 
// Function: get_parent 
// 
// Returns the parent object of the specified type, if any. Returns NULL, if no such parent
// is found. Specifying VMM_OBJECT returns the immediate parent of any type. 
// 
//|   
//|   class tb_env extends vmm_env;
//|      tr_scenario_gen gen1;
//|      function new(string inst, vmm_consensus end_vote);
//|         gen1.set_parent(this);
//|      endfunction
//|   endclass
//|   initial begin
//|      tb_env env;
//|      if (env.gen1.randomized_obj.get_parent() != env.gen1) begin
//|         `vmm_error(log, "Factory instance in atomic_gen returns wrong parent");
//|      end
//|   end
function vmm_object vmm_object::get_parent(type_e typ = VMM_OBJECT);
   vmm_object obj = this;

   while (obj._parent != null) begin
      if (typ == VMM_OBJECT ||
          obj._parent.get_type() == typ) return obj._parent;

      obj = obj._parent;
   end
   return null;
endfunction


// //////////////////////////////////////////// 
// Function: get_type 
// 
// Returns the type of this vmm_object extension. 
// Returns the VMM_OBJECT, if it is not one of the known VMM class extensions. VMM_UNKNOWN
// is purely an internal value, and is never returned. 
// 
//|   
//|   class tb_env extends vmm_env;
//|      tr_scenario_gen gen1;
//|      gen1.set_parent(this);
//|   endclass
//|   
//|   initial begin
//|      tb_env env;
//|      if (env.get_type() != VMM_ENV) 
//|         begin
//|            `vmm_error(log, "Wrong type returned from vmm_env
//|            instance");
//|         end
//|   end
function vmm_object::type_e vmm_object::get_type();
   // Find out -- and cache -- the object type
   begin
      vmm_scenario obj;
      if ($cast(obj, this)) begin
         return VMM_SCENARIO;
      end
   end
   begin
      vmm_data obj;
      if ($cast(obj, this)) begin
         return VMM_DATA;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_ms_scenario obj;
      if ($cast(obj, this)) begin
         return VMM_MS_SCENARIO;
      end
   end
`endif
   begin
      vmm_channel obj;
      if ($cast(obj, this)) begin
         return VMM_CHANNEL;
      end
   end
   begin
      vmm_notify obj;
      if ($cast(obj, this)) begin
         return VMM_NOTIFY;
      end
   end
   begin
      vmm_xactor obj;
      if ($cast(obj, this)) begin
         return VMM_XACTOR;
      end
   end
   begin
      vmm_subenv obj;
      if ($cast(obj, this)) begin
         return VMM_SUBENV;
      end
   end
   begin
      vmm_env obj;
      if ($cast(obj, this)) begin
         return VMM_ENV;
      end
   end
   begin
      vmm_consensus obj;
      if ($cast(obj, this)) begin
         return VMM_CONSENSUS;
      end
   end
`ifdef NOT_YET_IMPLEMENTED
   begin
      vmm_test obj;
      if ($cast(obj, this)) begin
         return VMM_TEST;
      end
   end
`endif

   // I give up!
   return VMM_OBJECT;
endfunction


// //////////////////////////////////////////// 
// Function: get_hier_inst_name 
// 
// Returns the vmm_log instance of this object, or the nearest enclosing object. If no
// vmm_log instance is available in the object genealogy, a default global vmm_log instance
// is returned. 
// 
//|   class ABC extends vmm_object;
//|      vmm_log log = new("ABC", "class");
//|      ...
//|      function vmm_log get_log();
//|         return this.log;
//|      endfunction
//|   ...
//|   endclass
//|   
//|   vmm_log test_log;
//|   ABC abc_inst = new("test_abc");
//|   initial begin
//|      test_log = abc_inst.get_log();
//|      ...
//|   end
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
function vmm_object::new(vmm_object parent = null
                         `VMM_OBJECT_BASE_NEW_ARGS);
      string space;
      bit ok;
      
      this.name = name;
      //if (name == "") `vmm_warning(this.log, "Object has no name. Please specify a name for the object");
      this.disable_hier_insert = disable_hier_insert;
      if (parent == null) begin
         //if parent is null then check if hierarchy insertion is disabled
         if (disable_hier_insert) return;
      end
      else if (parent == this) begin
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
                            
// //////////////////////////////////////////// 
// Function: set_object_name 
// 
// This method is used to set or replace the name of this object in the specified namespace.
// If no namespace is specified, the name of the object is replaced. If a name is not specified
// for a namespace, it defaults to the object name. Names in a named namespace may contain
// colons (:) to create additional levels of hierarchy, or may be empty to skip a level of
// hierarchy. A name starting with a caret (^) indicates that it is a root in the specified
// namespace. However, this does not apply to the object name where parentless objects
// create roots in the default namespace. 
// 
//|   class E extends vmm_object;
//|      ...
//|   endclass
//|   initial begin
//|      vmm_object obj;
//|      E e1 = new ("e1");
//|      create_namespace("NS1", 
//|         IN_BY_DEFAULT);
//|      ...
//|      obj = e1;
//|      obj.set_object_name ("new_e1","NS1");
//|      ...
//|   end
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
   
      
      if (parent == null) begin
         //check if this is vmm_data
         if (this.disable_hier_insert) return;
      end
      else if (this._parent == parent) return;  //nothing changed
      
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
         
         //in this case, check children threshhold
         if (do_object_thresh_check && this._parent.children.size() >= children_thresh) 
            `vmm_warning(this.log, `vmm_sformatf("The number of children of object [%s] passes the specified threshold ( = %0d ) indicating a potential garbage collection/memory leak problem. Please use vmm_object::kill_object() or increase the threshold.", this._parent.get_object_hiername(), children_thresh));
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
         
         //in this case, check root threshhold
         if (do_object_thresh_check && this.roots.size() >= root_thresh) 
            `vmm_warning(this.log, `vmm_sformatf("The number of root objects passes the specified threshold ( = %0d ) indicating a potential garbage collection/memory leak problem. Please use vmm_object::kill_object() or increase the threshold.", root_thresh));
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
         
         //in this case, check children threshhold
         if (do_object_thresh_check && this._parent.children.size() >= children_thresh) 
            `vmm_warning(this.log, `vmm_sformatf("The number of children of object [%s] passes the specified threshold ( = %0d ) indicating a potential garbage collection/memory leak problem. Please use vmm_object::kill_object() or increase the threshold.", this._parent.get_object_hiername(), children_thresh));
         
         return;
      end
   endfunction:set_parent_object
   
// //////////////////////////////////////////// 
// Function: get_parent_object 
// 
// Returns the parent object of this object for specified namespace, if any. Returns null,
// if no parent is found. A root object contains no parent. 
// 
//|   class C extends vmm_object;
//|      ...
//|   endclass
//|   class D extends vmm_object;
//|      C c1;
//|      function new(string name, vmm_object parent=null);
//|      c1 = new ("c1",this);
//|      endfunction
//|   endclass 
//|   
//|   initial begin
//|      vmm_object parent; 
//|      D d1 = new ("d1");
//|      parent = d1.c1.get_parent_object;
//|   end
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
   
// //////////////////////////////////////////// 
// Function: get_root_object 
// 
// Gets the root parent of this object, for the specified namespace. 
// 
//|   class C extends vmm_object;
//|      ...
//|   endclass
//|   class D extends vmm_object;
//|      C c1;
//|      function new(string name, vmm_object parent=null);
//|         c1 = new ("c1",this);
//|      endfunction
//|   endclass 
//|   class E extends vmm_object;
//|      D d1;
//|      function new(string name, vmm_object parent=null);
//|         ...
//|         d1 = new ("d1",this);
//|      endfunction
//|   endclass
//|   ...
//|   initial begin
//|      vmm_object root; 
//|      E e1 = new ("e1");
//|      root = e1.d1.c1.get_root_object;
//|      ...
//|   end
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
   
// //////////////////////////////////////////// 
// Function: get_num_children 
// 
// Gets the total number of root objects in the specified namespace. 
// 
//|   class D extends vmm_object;
//|      ...
//|   endclass
//|   class E extends vmm_object;
//|      D d1;
//|      D d2;
//|      function new(string name, vmm_object parent=null);
//|         ...
//|         d1 = new ("d1"); 
//|         d2 = new ("d2");
//|      endfunction 
//|   endclass
//|   ...
//|   int num_roots;
//|   initial begin
//|      E e1 = new ("e1");
//|      ...
//|      num_roots = E :: get_num_roots; //Returns 2
//|      ...
//|   end
   function int        vmm_object::get_num_children();
     return this.children.size();
   endfunction:get_num_children
   
// //////////////////////////////////////////// 
// Function: get_nth_child 
// 
// Returns the nth child of this object. Returns null, if there is no child. 
// 
//|   class C extends vmm_object;
//|      ...
//|   endclass
//|   class D extends vmm_object;
//|      ...
//|   endclass
//|   class E extends vmm_object;
//|      C c1;
//|      D d1;
//|      D d2;
//|      function new(string name, vmm_object parent=null);
//|         c1 = new ("c1",this);
//|         d1 = new ("d1"); 
//|         d2 = new ("d2",this);
//|      endfunction 
//|   endclass
//|   initial begin
//|      vmm_object obj;
//|      string name;
//|      E e1 = new ("e1");
//|      obj = e1.get_nth_child(0);
//|      name = obj.get_object_name();  //Returns c1
//|      ...
//|   end
   function vmm_object vmm_object::get_nth_child(int n);
      if (n < 0 || n >= this.children.size()) return null;
      return this.children[n];
   endfunction:get_nth_child
   
// //////////////////////////////////////////// 
// Function: get_object_name 
// 
// Gets the local name of this object, in the specified namespace. If no namespace is specified,
// then returns the actual name of the object. 
// 
//|   class C extends vmm_object;
//|      function new(string name, vmm_object parent=null);
//|         super.new (parent,name);
//|      endfunction
//|   endclass
//|   ...
//|   initial begin
//|      string obj_name;
//|      C c1 = new ("c1");
//|      ...
//|      obj_name = c1.get_object_name(); //Returns c1
//|      ...
//|   end
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
   
// //////////////////////////////////////////// 
// Function: get_object_hiername 
// 
// Gets the complete hierarchical name of this object in the specified namespace, relative
// to the specified root object. If no root object is specified, returns the complete hierarchical
// name of the object. The instance name is composed of the period-separated instance
// names of the message service interface of all the parents of the object. 
// 
//|   class D extends vmm_object;
//|      ...
//|   endclass
//|   class E extends vmm_object;
//|      D d1;
//|      function new(string name, vmm_object parent=null);
//|         ...
//|         d1 = new ("d1",this); 
//|      endfunction 
//|   endclass
//|   ...
//|   initial begin
//|      string hier_name;
//|      E e1 = new ("e1");
//|      ...
//|      hier_name = e1.d1.get_object_hiername();
//|      ...
//|   end
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
   
// //////////////////////////////////////////// 
// Function: find_child_by_name 
// 
// Finds the named object, interpreting the name as an absolute name in the specified namespace.
// If the name is a match pattern or regular expression, the first object matching the name
// is returned. 
// Returns null, if no object was found under the specified name. 
// 
//|   class D extends vmm_object;
//|      ...
//|   endclass
//|   class E extends vmm_object;
//|      D d1;
//|      function new(string name, vmm_object parent=null);
//|         ...
//|         d1 = new ("d1"); 
//|      endfunction 
//|   endclass
//|   ...
//|   initial begin
//|      vmm_object obj;
//|      ...
//|      obj = E :: find_object_by_name ("d1");
//|      ...
//|   end
   function vmm_object vmm_object::find_child_by_name(string name, string space = "");
      string hiername;
      `vmm_path_compiled compiled_hiername;
      `vmm_path_regexp compiled_pattern;

      compiled_pattern = vmm_path_match::compile_pattern(name, log);

      foreach(registered_objects[i]) begin
         if (!registered_objects[i].is_in_namespace(space)) continue;
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
         if (!registered_objects[i].is_in_namespace(space)) continue;
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
   
// //////////////////////////////////////////// 
// Function: get_nth_root 
// 
// Returns the nth root object in the specified namespace. Returns null, if there is no
// such root. 
// 
//|   class D extends vmm_object;
//|      ...
//|   endclass
//|   class E extends vmm_object;
//|      D d1;
//|      D d2;
//|      function new(string name, vmm_object parent=null);
//|         ...
//|         d1 = new ("d1"); 
//|         d2 = new ("d2");
//|      endfunction 
//|   endclass
//|   ...
//|   int num_roots;
//|   initial begin
//|      vmm_object root; 
//|      E e1 = new ("e1");
//|      ...
//|      root= E :: get_nth_root(0); //Returns d1
//|      ...
//|   end
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
   
// //////////////////////////////////////////// 
// Function: kill_object 
// 
// Constructs a new instance of this object, optionally specifying another object as
// its parent. The specified named cannot contain any colons (:). Specified argument
// disable_hier_insert indicates whether hierarchical insertion needs to be enabled
// or not. 
// 
//|   class A extends vmm_object;
//|      function new (string name, vmm_object parent=null);
//|         super.new (parent, name);
//|      endfunction
//|   endclass
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
   
// //////////////////////////////////////////// 
// Function: display 
// 
// Displays the image returned by type_e to the standard output. Each
// line of the output will be prefixed with the specified argument prefix. 
// If this method conflicts with a previously declared method in a class, which is now based
// on the vmm_object class, it can be removed by defining the VMM_OBJECT_NO_DISPLAY
// symbol at compile-time. 
// 
//|   
//|   class trans_data extends vmm_data;
//|      byte data;
//|      ...
//|   endclass
//|   
//|   initial begin
//|      trans_data trans;
//|      trans.display("Test Trans: ");
//|   end
   function void       vmm_object::display(string prefix = "");
      $display(this.psdisplay(prefix));
   endfunction :display
   
   function string     vmm_object::psdisplay(string prefix = "");
      $sformat(psdisplay, "%sObject \"%s\"",  prefix,this.get_object_hiername());
   endfunction:psdisplay
   
// //////////////////////////////////////////// 
// Function: print_hierarchy 
// 
// Creates a human-readable description of the content of this object. Each line of the
// image is prefixed with the specified prefix. 
// Example 
// class D extends vmm_object; 
// ... 
// function string psdisplay(string prefix = ""); 
// ... 
// endfuntion 
// endclass 
// ... 
// vmm_log log = new ("Test", "main"); 
// initial begin 
// D d1 = new ("d1"); 
// ... 
// `vmm_note (log, d1.psdisplay); 
// ... 
// end 
// 
// 
//|   class D extends vmm_object;
//|      ...
//|   endclass
//|   class E extends vmm_object;
//|      D d1;
//|      function new(string name, vmm_object parent=null);
//|         ...
//|         d1 = new ("d1",this); 
//|      endfunction 
//|   endclass
//|   initial begin
//|      E e1 = new ("e1");
//|      ...
//|      E :: print_hierarchy;
//|      ...
//|   end
//|    psdisplay
//|   Creates a description of the object.
//|   SystemVerilog
   function void       vmm_object::print_hierarchy(vmm_object root = null, bit verbose = 0);
      if (root == null) begin
         foreach (roots[i]) begin
            print_hierarchy(roots[i], verbose);
            $write("\n");
         end
         return;
      end
      
      root.print_tree(0, verbose);
   endfunction:print_hierarchy

// //////////////////////////////////////////// 
// Function: implicit_phasing 
// 
// If the is_on argument is false, inhibits the implicit phasing for this object and all
// of its children objects. Used to prevent a large object hierarchy that does not require
// phasing from being needlessly walked by the implicit phaser (for example, a RAL model).
// By default, implicit phasing is enabled. 
// 
//|   class subsys_env extends vmm_subenv;
//|      ...
//|   endclass
//|   
//|   class sys_env extends vmm_subenv;
//|      subsys_env subenv1;
//|      ...
//|      function void build();
//|         ...
//|         subenv1 = new ("subenv1", "subenv1");
//|         subenv1.set_parent_object(this);
//|         subenv1.implicit_phasing(0);
//|         ...
//|      endfunction
//|      ...
//|   endclass
   function void       vmm_object::implicit_phasing(bit is_on);
      this.implicit_phasing_enabled = is_on;
   endfunction:implicit_phasing
   
// //////////////////////////////////////////// 
// Function: is_implicitly_phased 
// 
// Returns true, if the implicit phasing is enabled for this object. 
// 
//|   class subsys_env extends vmm_subenv;
//|      ...
//|   endclass
//|   
//|   class sys_env extends vmm_env;
//|      subsys_env subenv1;
//|      ...
//|      function void build();
//|         ...
//|         subenv1 = new ("subenv1", "subenv1");
//|         subenv1.set_parent_object(this);
//|         subenv1.implicit_phasing(0);
//|         if(subenv1.is_implicitly_phased)
//|            `vmm_error(log, "Implict Phasing for subenv1 not
//|               disabled");
//|         ...
//|      endfunction	   
//|      ...
//|   endclass
   function bit        vmm_object::is_implicitly_phased();
      return this.implicit_phasing_enabled;
   endfunction:is_implicitly_phased


// //////////////////////////////////////////// 
// Function: create_namespace 
// 
// Defines a namespace with the specified default object inclusion policy. A namespace
// must be previously created using this method, before it can be used or referenced. Returns
// true, if the namespace was successfully created. The empty name space ("") is reserved
// and cannot be defined. 
// 
//|   class A extends vmm_object;
//|      function new (string name, vmm_object parent=null);
//|         super.new (parent, name);
//|         create_namesapce("NS1",
//|            IN_BY_DEFAULT);
//|      endfunction
//|   endclass
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
   
// //////////////////////////////////////////// 
// Function: get_namespaces 
// 
// This method returns all namespaces created by the create_namespace() method that
// belong to a dynamic array of strings as specified by names[]. 
// 
//|   initial begin
//|      string ns_array[];
//|      ...
//|      get_namespaces(ns_array); 
//|      ...
//|   end
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

   function void vmm_object::register_object(vmm_object obj);
      if (obj == null) begin 
         `vmm_error(log,"null objects cannot be registered");
         return;
      end
      foreach (registered_objects[i]) begin
         if (registered_objects[i] == obj) begin
            return;
         end
      end
      registered_objects.push_back(obj);
   endfunction:register_object

   function void vmm_object::unregister_object(vmm_object obj);
      foreach (registered_objects[i]) begin
         if (registered_objects[i] == obj) begin
            registered_objects.delete(i);
            return;
         end
      end
   endfunction:unregister_object


// //////////////////////////////////////////// 
// Function: is_parent_of 
// 
// Returns true, if the specified object is a parent of this object under specified argument
// space namespace. 
// 
//|   class sub extends vmm_subenv;
//|      ...
//|   endclass
//|   
//|   class tb_env extends vmm_env;
//|      sub s1 ;
//|      ...
//|      virtual function void build();
//|         super.build();
//|         s1 = new ("s1");
//|         s1.set_parent(this);
//|         if (!this.is_parent_of(s1))	
//|            `vmm_error(log, "Unable to set parent for s1");
//|         ...
//|      endfunction
//|   endclass
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
   
   function void    vmm_object::print_tree(int level = 0, bit verbose = 0);
      int i;
      vmm_object child;
      vmm_notify tmp_notify;
      vmm_consensus tmp_consensus;
`ifndef NO_VMM12_PHASING
      vmm_phase_def tmp_phase_def;
`endif
      bit print_it;
      
      print_it = 1;
      
      if (verbose == 0) begin
         if ( $cast(tmp_notify, this) ||
              $cast(tmp_consensus, this) ||
`ifndef NO_VMM12_PHASING
              $cast(tmp_phase_def, this) ||
`endif
              this.get_object_name() == "" ||
              this.get_object_name() == "Anonymous" ) print_it = 0;
      end
      
      if (print_it) begin
         if (level > 1) repeat (level-1) $write("|  ");
         if (level > 0) $write("|--");
         $write("[%s]\n", this.get_object_name());
      end
      
      i = 0;
      child = this.get_nth_child(i++);
      while (child != null) begin
         child.print_tree(level+1, verbose);
         child = this.get_nth_child(i++);
      end

   endfunction:print_tree


`endif // VMM_OBJECT__SV
