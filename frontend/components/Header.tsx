export default function Header() {
    return (
        <header className="flex items-center justify-between px-8 py-4 bg-gray-900 border-b border-gray-800">
            <div className="flex items-center space-x-2">
                <div className="w-8 h-8 bg-gradient-to-br from-blue-500 to-purple-600 rounded-lg"></div>
                <h1 className="text-2xl font-bold bg-clip-text text-transparent bg-gradient-to-r from-white to-gray-400">
                    Veritas AI
                </h1>
            </div>
            <div className="flex items-center space-x-2 bg-gray-800 px-3 py-1 rounded-full border border-gray-700">
                <div className="w-2 h-2 bg-green-400 rounded-full animate-pulse"></div>
                <span className="text-xs text-gray-300 font-mono">Gemini 3.0 Pro</span>
            </div>
        </header>
    );
}
