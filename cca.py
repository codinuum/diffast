#!/usr/bin/env python3

'''
  A driver script for Diff/AST container image

  Copyright 2025 Codinuum Software Lab <https://codinuum.com>

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
'''

import os
import sys
import time
# import shutil
from datetime import datetime, timedelta
from subprocess import run
# from threading import Thread
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter

# IMAGE_NAME = 'codinuum/diffast'
IMAGE_NAME = 'diffast5'

#

CCA_HOME = '/opt/cca'
CCA_VAR = '/var/lib/cca'
CCA_LOG_DIR = '/var/log/cca'

CCA_SOURCE_DIR = CCA_VAR+'/source'
CCA_CACHE_DIR = CCA_VAR+'/cache'

CCA_WORK_DIR_NAME = '__CCA__'

CONTAINER_CMD = 'docker'

TIMEOUT = 5
BUFSIZE = 0  # unbuffered
STAT_NAME = 'status'

DEFAULT_CACHE_DIR = os.path.join(os.environ['HOME'], '.cca', 'cache')

# WIN_HOST_FLAG = sys.platform.startswith('win')

# timezone

TZ = None

if time.timezone != 0:
    SIGN = '+' if time.timezone > 0 else '-'

    STDOFFSET = timedelta(seconds=-time.timezone)
    if time.daylight:
        DSTOFFSET = timedelta(seconds=-time.altzone)
    else:
        DSTOFFSET = STDOFFSET

    dt = datetime.now()
    tt = (dt.year, dt.month, dt.day,
          dt.hour, dt.minute, dt.second,
          dt.weekday(), 0, 0)
    stamp = time.mktime(tt)
    tt = time.localtime(stamp)

    isdst = tt.tm_isdst > 0

    tzname = None
    offset = 0

    if isdst:
        tzname = time.tzname[1]
        offset = DSTOFFSET
    else:
        tzname = time.tzname[0]
        offset = STDOFFSET

    TZ = f'{tzname}{SIGN}{offset}'

###


def progress(proc, stat_path, timeout=TIMEOUT):
    stat_mtime = None

    print('\nMonitoring thread started.')

    while True:
        try:
            st = os.stat(stat_path)
            if st.st_mtime != stat_mtime and st.st_size > 0:
                with open(stat_path, 'r') as f:
                    mes = f.read()
                    print(f'[{mes}]')

                stat_mtime = st.st_mtime

        except OSError:
            pass

        if proc.poll() is not None:
            break

    proc.wait()
    if proc.returncode > 0:
        print(f'Execution failed: {proc.returncode}')


def ensure_dir(dpath):
    if not os.path.isdir(dpath):
        try:
            os.makedirs(dpath)
        except Exception:
            raise


def get_viewer_app_path(diffviewer_dir):
    dpath = os.path.join(os.path.dirname(sys.argv[0]), diffviewer_dir)
    apath = None
    for x in os.listdir(dpath):
        if x.startswith('DiffViewer'):
            apath = os.path.join(dpath, x, 'DiffViewer.app')
            if os.path.exists(apath):
                break
    return apath


def get_image_name(image_name, devel=False):
    suffix = ''
    if devel:
        suffix = ':devel'
    image = image_name+suffix
    return image


def run_diffast(container_cmd, original, modified,
                cache=DEFAULT_CACHE_DIR, clear_cache=False, view=False,
                dry_run=False, devel=False, image=IMAGE_NAME,
                verbose=False, debug=False):

    if dry_run:
        verbose = True

    original = os.path.abspath(original)
    modified = os.path.abspath(modified)
    cache = os.path.abspath(cache)

    if not dry_run:
        ensure_dir(cache)

    cca_cmd_path = f'{CCA_HOME}/bin/diffast.exe'
    cca_cmd = cca_cmd_path
    if clear_cache:
        cca_cmd += ' -clearcache'

    cca_cmd += f' -cache {CCA_CACHE_DIR}'

    orig_dir = os.path.dirname(original)
    mod_dir = os.path.dirname(modified)

    common_path = os.path.commonpath([orig_dir, mod_dir])

    orig_path = CCA_SOURCE_DIR+'/'+os.path.relpath(original, start=common_path)
    mod_path = CCA_SOURCE_DIR+'/'+os.path.relpath(modified, start=common_path)

    cca_cmd += f' {orig_path} {mod_path}'

    vol_opt = f'-v "{common_path}:{CCA_SOURCE_DIR}"'
    vol_opt += f' -v "{cache}:{CCA_CACHE_DIR}"'

    run_cmd = f'{container_cmd} run'
    run_cmd += ' --rm'
    run_cmd += ' -t'

    if TZ:
        run_cmd += f' -e "TZ={TZ}"'

    run_cmd += f' {vol_opt}'
    run_cmd += f' {get_image_name(image, devel=devel)} {cca_cmd}'

    if verbose:
        print(run_cmd)

    if not dry_run:
        try:
            _ = run(run_cmd,
                    bufsize=BUFSIZE, shell=True, universal_newlines=True)

            if view:
                app_path = get_viewer_app_path('diffviewer')
                if app_path is not None:
                    cache_opt = f' --cache {cache}'
                    files_opt = f' --file0 {original} --file1 {modified}'
                    view_cmd = (f'open -n {app_path}'
                                f' --args{cache_opt}{files_opt}')
                    if verbose:
                        print(view_cmd)
                    _ = run(view_cmd, shell=True)
                else:
                    print('DiffViewer not found. See diffviewer/README.md.')

        except (KeyboardInterrupt, SystemExit):
            print('Interrupted.')

        except OSError as e:
            print(f'Execution failed: {e}')


def gen_work_dir_name():
    dt = datetime.now()
    ts = (f'{dt.year:04}{dt.month:02}{dt.day:02}'
          f'{dt.hour:02}{dt.minute:02}{dt.second:02}')
    dn = f'{CCA_WORK_DIR_NAME}{ts}'
    return dn


def update(args):
    cmd = (f'{args.container_cmd} pull'
           f' {get_image_name(args.image, devel=args.devel)}')
    if args.verbose or args.dry_run:
        print(cmd)
    if not args.dry_run:
        try:
            run(cmd, shell=True)
        except OSError as e:
            print(f'Execution failed: {e}')


def diffast(args):
    run_diffast(args.container_cmd,
                args.original, args.modified,
                cache=args.cache, clear_cache=args.force, view=args.view,
                dry_run=args.dry_run, devel=args.devel, image=args.image,
                verbose=args.verbose, debug=args.debug)


def main():
    formatter = ArgumentDefaultsHelpFormatter

    parser = ArgumentParser(description='A Diff/AST driver',
                            add_help=False,
                            formatter_class=formatter)

    parser.add_argument('-n', '--dry-run', dest='dry_run', action='store_true',
                        help='only print container commands')

    parser.add_argument('--container-command', dest='container_cmd',
                        metavar='CMD', default=CONTAINER_CMD,
                        help='specify container command')

    parser.add_argument('-i', '--image', dest='image', type=str,
                        metavar='IMAGE', default=IMAGE_NAME,
                        help='specify container image')

    parser.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                        help='enable verbose printing')

    parser.add_argument('-d', '--debug', dest='debug', action='store_true',
                        help='enable debug printing')

    parser.add_argument('-x', '--experimental', dest='devel',
                        action='store_true',
                        help='use experimental image')

    p = ArgumentParser(add_help=True)

    subparsers = p.add_subparsers(title='subcommands')

    # Docker image update

    parser_update = subparsers.add_parser('update',
                                          description='Update docker image',
                                          parents=[parser],
                                          formatter_class=formatter)

    parser_update.set_defaults(func=update)

    # Diff/AST

    parser_diffast = subparsers.add_parser('diffast',
                                           description='Compare two programs',
                                           parents=[parser],
                                           formatter_class=formatter)

    parser_diffast.add_argument('original', type=str, metavar='ORIGINAL',
                                help='original source file')

    parser_diffast.add_argument('modified', type=str, metavar='MODIFIED',
                                help='modified source file')

    parser_diffast.add_argument('--view', dest='view', action='store_true',
                                help='launch DiffViewer after comparison')

    parser_diffast.add_argument('-f', '--force', dest='force',
                                action='store_true',
                                help='force comparison (overwrite cache)')

    parser_diffast.add_argument('-c', '--cache', dest='cache', type=str,
                                metavar='DIR', default=DEFAULT_CACHE_DIR,
                                help='result cache directory')

    parser_diffast.set_defaults(func=diffast)

    #

    args = p.parse_args()

    try:
        args.func(args)
    except Exception:
        # raise
        p.print_help()


if __name__ == '__main__':
    main()
