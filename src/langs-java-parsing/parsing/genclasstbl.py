#!/usr/bin/env python3
#
#   Copyright 2012-2025 Codinuum Software Lab <https://codinuum.com>
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#

import os
import sys
import subprocess

output_file_name = 'classtbl.ml'

classpath_tbl = {
    'linux': ['/usr/lib/jvm/java-11-openjdk-amd64/jre/lib',
              '/usr/lib/jvm/java-11-openjdk/jre/lib',
              '/usr/lib/jvm/java-8-openjdk-amd64/jre/lib',
              '/usr/lib/jvm/java-8-openjdk/jre/lib',
              '/usr/lib/jvm/java-7-openjdk-amd64/jre/lib',
              '/usr/lib/jvm/java-7-openjdk/jre/lib',
              '/usr/lib/jvm/java-6-openjdk-amd64/jre/lib',
              '/usr/lib/jvm/java-6-openjdk/jre/lib',
              ],
    'darwin': ['/Library/Java/JavaVirtualMachines/openjdk-17.jdk/Contents/Home/lib',
               '/Library/Java/JavaVirtualMachines/openjdk-11.jdk/Contents/Home/lib',
               '/Library/Java/JavaVirtualMachines/zulu8/jre/lib',
               ],
    }

core_jars = ['rt.jar', 'classes.jar', 'dt.jar', 'jce.jar']

###

jar_cmd_fmt = 'jar tf %s'

template_upper = '''
module Xset = Diffast_misc.Xset
let stdtbl =
  let pmap =
      [
'''

template_lower = '''
      ]
  in
  let tbl = Hashtbl.create 0 in
  List.iter
    (fun (pname, llist) ->
      let s = Xset.create (List.length llist) in
      List.iter
        (fun lname ->
          Xset.add s lname
        ) llist;
      Hashtbl.add tbl pname s
    ) pmap;
  tbl
'''


def getjars():
    jars = []
    cps = classpath_tbl[sys.platform]
    if cps:
        for cp in cps:
            for core_jar in core_jars:
                jar = os.path.join(cp, core_jar)
                if os.path.exists(jar):
                    jars.append(jar)

    return jars


def gen(jars):

    mapping = {}  # package name -> local name list

    for jar in jars:

        cmd = jar_cmd_fmt % jar

        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE,
                                close_fds=True)
        f = proc.stdout

        for l in f:
            line = l.rstrip().decode('utf-8')
            if line.endswith('.class'):
                if True:  # line.find('$') == -1:
                    s = os.path.splitext(line)[0]
                    cname = os.path.basename(s)
                    pname = os.path.dirname(s).rstrip('/').replace('/', '.')
                    try:
                        mapping[pname].append(cname)
                    except KeyError:
                        mapping[pname] = [cname]

    ofile = open(output_file_name, 'w')

    ofile.write(template_upper)

    for pname in mapping.keys():

        ofile.write('"%s", [\n' % pname)

        for cname in mapping[pname]:
            ofile.write('"%s";\n' % cname)

        ofile.write('];\n')

    ofile.write(template_lower)

    ofile.close()


def main():
    jars = getjars()

    for jar in jars:
        print('using "%s"' % jar)

    gen(jars)


if __name__ == '__main__':
    main()
