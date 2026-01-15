import { Eye } from "lucide-react";

export default function Header() {
    return (
        <header className="flex items-center justify-between px-8 py-4 bg-gray-900 border-b border-gray-800">
            <div className="flex items-center space-x-3">
                <div className="bg-gradient-to-br from-blue-500 to-purple-600 p-2 rounded-lg">
                    <Eye className="w-6 h-6 text-white" />
                </div>
                <h1 className="text-3xl font-bold tracking-widest bg-clip-text text-transparent bg-gradient-to-r from-white to-gray-400 font-sans">
                    ARGUS
                </h1>
            </div>
            <div className="flex items-center space-x-2 bg-gray-800 px-3 py-1 rounded-full border border-gray-700">
                <div className="w-2 h-2 bg-green-400 rounded-full animate-pulse"></div>
                <span className="text-xs text-gray-300 font-mono">Gemini 3.0 Pro</span>
            </div>
        </header>
    );
}
